-- Prove2me | Theorems.Thm_SemAC02_lemma_4_9_product_approximation
-- name    : SemAC02.lemma_4_9_product_approximation
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:29:48.101625+00:00
-- url     : https://prove2.me/theorems/195984ee-6fff-4388-bbbc-dee415177a6c
-- title:
--   Lemma 4.9 — approximation of a product with an error of small rank
-- statement:
--   Let $n,h\ge1$, $N=nh$, partition the variables into parts $V_1,\dots,V_n$ of size $h$, let $F_0$ consist of the products of distinct variables in the same part, and work in $\mathcal B_{F_0}=\mathcal B_N/\langle F_0\rangle$. Let $1\le w\le k\le n$ and $r\ge0$ be integers and $T=\prod_{j\in J}g_j$ with $\deg g_j\le w$. Then there are $q_1,\dots,q_r\in\operatorname{span}\{1+g_j:j\in J\}$ such that the approximator $a=\prod_{\ell=1}^r(1+q_\ell)$ has degree at most $rw$ and satisfies $aT=T$, and the error operator $\mathrm{Err}_T(f)=f\,\mathrm{err}_T$, $\mathrm{err}_T=T+a$, on $\mathcal B_{F_0}^{\le k}$ satisfies
--   $$
--   \operatorname{rank}(\mathrm{Err}_T)=\dim\bigl(\mathrm{err}_T\,\mathcal B_{F_0}^{\le k}\bigr)\le H_{F_0}(k)\Bigl(1-\frac{H_{F_0}(k-w)}{2H_{F_0}(k)}\Bigr)^{r}.
--   $$
--   If moreover $2w\le k\le n/3$, then
--   $$
--   \operatorname{rank}(\mathrm{Err}_T)\le\frac{2\binom nk h^k}{\exp\bigl(\frac r4\,(\frac k{2N})^w\bigr)} .
--   $$
--
--   This is the Razborov–Smolensky step: a product of low-degree factors agrees with a low-degree approximator outside an error whose multiples span a small space.
--
--   Differences from the source:
--   - encoding: elements of B_{F₀} with their degree; g_j of degree ≤ w; q_ℓ in span{1 + g_j} → functions on Ω (restrOmega of polynomial representatives); g_j given by representatives of totalDegree ≤ w; q_ℓ in the span of those representatives; deg a bounded by the totalDegree of the product; reason: every element of B_{F₀} of degree ≤ w has a representative of total degree ≤ w, and a span of representatives maps onto the span in B_{F₀}; same instances
--   - encoding: variables partitioned into V₁, …, V_n of size h; k ≤ n/3 → variables Fin n × Fin h; 3k ≤ n; reason: same instances
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Lemma 4.9, p.30 (PDF p.32)

import Mathlib
import Definitions.Def_SemAC02_nDivision

namespace SemAC02

open MvPolynomial

/-- **Lemma 4.9 (Approximation of T)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission), Lemma 4.9, p.30): let `n, h ≥ 1` be
integers, put `N = nh`, and partition the variables into `V₁, …, V_n`, each of size `h`. Let `F₀`
consist of all products `xy` of distinct variables in the same part, and work in
`B_{F₀} = B_N/⟨F₀⟩`. Let `1 ≤ w ≤ k ≤ n` and `r ≥ 0` be integers, and let `T = ∏_{j∈J} g_j`,
where `deg(g_j) ≤ w` for each `j ∈ J`. Then there exist `q₁, …, q_r ∈ span{1 + g_j : j ∈ J}`
such that the approximator `a := ∏_{ℓ=1}^r (1 + q_ℓ)` has degree at most `rw` and satisfies
`aT = T`. Define the error polynomial `err_T := T + a` and the error operator
`Err_T : B_{F₀}^{≤k} → B_{F₀}`, `Err_T(f) := f err_T`. Then
`rank(Err_T) = dim(err_T B_{F₀}^{≤k}) ≤ H_{F₀}(k) (1 − H_{F₀}(k − w)/(2H_{F₀}(k)))^r`.
If additionally `2w ≤ k ≤ n/3`, then
`rank(Err_T) ≤ 2 C(n,k) h^k / exp((r/4)(k/(2N))^w)`.

**Formalization Note** The variables are `Fin n × Fin h` (part `i` is `{i} × Fin h`); `B_{F₀}` is
the space of functions on `Ω` (at most one `1` per part), an element being restricted from any
polynomial representing it (`restrOmega`), and degree is the least total degree of a
representative. The `g_j` are given by representatives of total degree `≤ w`, `J` a finite type;
`q_ℓ` are taken in the span of the representatives `1 + g_j`. `err_T B_{F₀}^{≤k}` is the image of
`B_{F₀}^{≤k}` under multiplication by `err_T`; `k ≤ n/3` is `3k ≤ n`. -/
theorem lemma_4_9_product_approximation (n h : ℕ) (hn : 1 ≤ n) (hh : 1 ≤ h) (w k r : ℕ)
    (hw : 1 ≤ w) (hwk : w ≤ k) (hkn : k ≤ n) {J : Type} [Fintype J]
    (gs : J → MvPolynomial (Fin n × Fin h) (ZMod 2)) (hgs : ∀ j, (gs j).totalDegree ≤ w) :
    ∃ q : Fin r → MvPolynomial (Fin n × Fin h) (ZMod 2),
      (∀ l, q l ∈ Submodule.span (ZMod 2) (Set.range fun j => 1 + gs j)) ∧
      (∏ l, (1 + q l)).totalDegree ≤ r * w ∧
      restrOmega n h ((∏ l, (1 + q l)) * ∏ j, gs j) = restrOmega n h (∏ j, gs j) ∧
      (Module.finrank (ZMod 2) ((BleF0 n h k).map (LinearMap.mulLeft (ZMod 2)
          (restrOmega n h ((∏ j, gs j) + ∏ l, (1 + q l))))) : ℝ) ≤
        (HF0 n h k : ℝ) * (1 - (HF0 n h (k - w) : ℝ) / (2 * (HF0 n h k : ℝ))) ^ r ∧
      (2 * w ≤ k → 3 * k ≤ n →
        (Module.finrank (ZMod 2) ((BleF0 n h k).map (LinearMap.mulLeft (ZMod 2)
          (restrOmega n h ((∏ j, gs j) + ∏ l, (1 + q l))))) : ℝ) ≤
          2 * (n.choose k : ℝ) * (h : ℝ) ^ k /
            Real.exp ((r : ℝ) / 4 * ((k : ℝ) / (2 * ((n * h : ℕ) : ℝ))) ^ w)) := by sorry

end SemAC02
