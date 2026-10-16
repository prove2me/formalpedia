-- Prove2me | Theorems.Thm_SubsetShrink_DFO_proposition_1
-- name    : SubsetShrink.DFO.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T19:31:25.734275+00:00
-- url     : https://prove2.me/theorems/7d95530a-da7f-4be0-8ecd-8f1b24910507
-- title:
--   Proposition 1, p. 9 (tie-corrected) — closed form of the thresholding operator S(u; k; λℓ_q) for q = 1, 2
-- statement:
--   Let $u\in\mathbb R^p$, $1\le k\le p$, $\lambda\ge0$, $q\in\{1,2\}$, and let $\hat\beta\in\mathrm S(u;k;\lambda\ell_q)$, a minimizer of $\tfrac12\|\beta-u\|_2^2+\lambda\|\beta\|_q$ over $\|\beta\|_0\le k$. Then there is an ordering $(1),\dots,(p)$ of the indices with $|u_{(1)}|\ge|u_{(2)}|\ge\dots\ge|u_{(p)}|$ such that, writing $T=\{(1),\dots,(k)\}$:
--
--   1. if $q=1$,
--   $$\hat\beta_i=\begin{cases}\operatorname{sgn}(u_i)\max\{|u_i|-\lambda,0\}, & i\in T,\\ 0, & \text{otherwise};\end{cases}$$
--   2. if $q=2$,
--   $$\hat\beta_i=\begin{cases}\dfrac{u_i}{\tau_u}\max\{\tau_u-\lambda,0\}, & i\in T,\\ 0, & \text{otherwise},\end{cases}\qquad \tau_u=\sqrt{\textstyle\sum_{i=1}^k u_{(i)}^2}.$$
--
--   The DFO update (14) is therefore computable in closed form: keep the $k$ largest entries in magnitude and soft-threshold them, coordinatewise for $\ell_1$ and as a group for $\ell_2$.
--
--   **Formalization Note** The page says "Let $(1),\dots,(p)$ be a permutation … sorted … Then any $\hat\beta$ … is given by (12)/(13)". For a fixed sorting order this fails under ties: for $u=(1,1)$, $k=1$, $\lambda=0$ both $(1,0)$ and $(0,1)$ are minimizers. The statement therefore asserts that *some* sorting order exists for each minimizer. Both parts are labelled "(a)" on the page. The ordering is a permutation $\pi$ of `Fin p` with $|u_{\pi(0)}|\ge|u_{\pi(1)}|\ge\cdots$, so the paper's $(j)$ is $\pi(j-1)$. When $\tau_u=0$, $u_i/\tau_u$ is $0$, both in Lean and by the paper's convention $0/0=0$ (p. 13); the formula then gives $0$. $\operatorname{sgn}$ is `Real.sign`, with $\operatorname{sgn}(0)=0$. This result is a companion: the proof of Proposition 2 does not use it.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 9, Proposition 1, (12)–(13)

import Mathlib
import Definitions.Def_SubsetShrink_DFO_Model

namespace SubsetShrink.DFO

/-- Proposition 1, p. 9 (Mazumder, Radchenko & Dedieu, arXiv:1708.03288v4), with the tie
pin (slip 6). Let `u ∈ ℝᵖ`, `1 ≤ k ≤ p`, `λ ≥ 0`, `q ∈ {1, 2}`, and let
`β̂ ∈ S(u; k; λℓ_q)`. Then there is a permutation `π` of the coordinates sorting `|u|`
non-increasingly (`|u_{π 0}| ≥ |u_{π 1}| ≥ …`; the paper's `(j)` is `π (j − 1)`) such that,
with `T = {π 0, …, π (k−1)}` the indices of the `k` largest entries in magnitude,

(a) if `q = 1`: `β̂ᵢ = sgn(uᵢ) max{|uᵢ| − λ, 0}` for `i ∈ T` and `β̂ᵢ = 0` otherwise ((12));
(b) if `q = 2`: `β̂ᵢ = (uᵢ/τ_u) max{τ_u − λ, 0}` for `i ∈ T` and `β̂ᵢ = 0` otherwise ((13)),
    where `τ_u = √(∑_{j=1}^k u_{(j)}²)`. If `τ_u = 0`, `uᵢ/τ_u` is read as `0` (Lean's division,
    and the paper's `0/0 = 0` convention, p. 13); the formula then gives `0`.

Both parts are labelled "(a)" on the page. For a *fixed* sorting permutation the printed claim
fails under ties (`u = (1, 1)`, `k = 1`), hence the existential. -/
theorem proposition_1 {p : ℕ} (u : E p) (k : ℕ) (lam : ℝ) (q : ℕ)
    (hq : q = 1 ∨ q = 2) (hk : 1 ≤ k) (hkp : k ≤ p) (hlam : 0 ≤ lam)
    (βhat : E p) (hβ : IsThresh u k lam q βhat) :
    ∃ π : Equiv.Perm (Fin p), Antitone (fun j : Fin p => |u (π j)|) ∧
      (q = 1 → ∀ i : Fin p, βhat i =
        if i ∈ (Finset.univ.filter (fun j : Fin p => j.val < k)).image π
        then Real.sign (u i) * max (|u i| - lam) 0 else 0) ∧
      (q = 2 → ∀ i : Fin p, βhat i =
        if i ∈ (Finset.univ.filter (fun j : Fin p => j.val < k)).image π
        then u i / Real.sqrt (∑ j ∈ Finset.univ.filter (fun j : Fin p => j.val < k), u (π j) ^ 2)
          * max (Real.sqrt (∑ j ∈ Finset.univ.filter (fun j : Fin p => j.val < k), u (π j) ^ 2)
            - lam) 0
        else 0) := by sorry

end SubsetShrink.DFO
