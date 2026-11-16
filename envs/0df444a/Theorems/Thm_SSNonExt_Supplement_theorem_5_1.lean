-- Prove2me | Theorems.Thm_SSNonExt_Supplement_theorem_5_1
-- name    : SSNonExt.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T18:58:25.029577+00:00
-- url     : https://prove2.me/theorems/042600e0-601c-434c-9ac6-5d2d4a68a286
-- title:
--   Theorem 5.1 — perfect $r$-out-of-$r$ sharing on flat sources with extraction error $\ge 1/(2(2^r-1))$, tight
-- statement:
--   Let $r\ge2$ and $b\ge r$. Let $V=\mathbb F_{2^b}$, $B=2^b$, $N=B^{r-1}$, and let $\gamma_1,\dots,\gamma_r\in V$ be linearly independent over $\mathbb F_2$. Let $\Pi_b^{(r)}$ be the $r$-out-of-$r$ scheme of display (7) with key set $\mathcal K^{(r)}$, and $\mathcal S_b^{(r)}=\{P_T:T\subseteq V^{r-1}\}$ its source class of display (8). Then $\Pi_b^{(r)}$ is a **perfectly correct** $r$-out-of-$r$ scheme for $b$-bit messages (all $r$ parties together reconstruct the message, for every message and every key) that is **perfectly private** for $\mathcal S_b^{(r)}$ (for every $P\in\mathcal S_b^{(r)}$ and every set of fewer than $r$ parties, the joint law of their shares is the same for every message), and:
--
--   1. each share has $b+1$ bits ($|\{0,1\}\times V|=2^{b+1}$), and $|\mathcal K^{(r)}|=(2^r-1)2^{(r-1)b}$;
--   2. every $P\in\mathcal S_b^{(r)}$ is uniform on a set $Z$ of keys with $(2^{r-1}-1)N\le|Z|\le2^{r-1}N$, and $H_\infty(P)\ge(r-1)b+\log_2(2^{r-1}-1)$;
--   3. for every $\ell\ge1$ and every function $\mathrm{Ext}:\mathcal K^{(r)}\to\{0,1\}^\ell$,
--   $$\max_{P\in\mathcal S_b^{(r)}}\mathrm{TV}\big(\mathrm{Ext}(K),U_\ell\big)\ge\frac1{2(2^r-1)},\qquad K\sim P;$$
--   4. for $\ell=1$ some function of the index alone attains equality in item 3: there is $g:V^{r-1}\to\{0,1\}$ such that $\mathrm{Ext}(u,S)=g(u)$ has error at most $1/(2(2^r-1))$ on every $P\in\mathcal S_b^{(r)}$ and exactly $1/(2(2^r-1))$ on some $P\in\mathcal S_b^{(r)}$.
--
--   For $r=2$ the bound is $1/6$, as in Theorem 1.1, and for $r=3$ it is $1/14$. The theorem shows that the phenomenon of the main result persists for every number of parties when all of them are needed to reconstruct.
--
--   **Formalization Note** Correctness and privacy are the published Definition 2.1 predicates `PerfectlyCorrect r` and `IsPrivate r 0` (TV $=0$ for every coalition of fewer than $r$ parties, the empty one included). TV is the $\tfrac12\ell^1$ distance, logarithms are base 2, $\{0,1\}^\ell$ is `Fin ℓ → Bool`, and linear independence is over `ZMod 2`.
--
--   Differences from the source:
--   - generalization: fix γ_1, …, γ_r linearly independent over 𝔽_2 → the theorem holds for every γ : Fin r → 𝔽_{2^b} linearly independent over ZMod 2; reason: the paper's choice is arbitrary; such γ exist since b ≥ r, so the statement specializes to the paper's
--   - encoding: each share has b + 1 bits → Fintype.card (Share b) = 2^(b+1); reason: the share alphabet is {0,1} × 𝔽_{2^b}
--   - encoding: N = B^{r−1} → (2^b)^(r−1); reason: definition of N
--   - encoding: max_{P∈𝒮_b^{(r)}} TV(Ext(K), U_ℓ) ≥ 1/(2(2^r − 1)) → ∃ P ∈ 𝒮_b^{(r)} with TV(Ext(K), U_ℓ) ≥ 1/(2(2^r − 1)); reason: the class is finite and nonempty, so the maximum is attained
--   - encoding: some function of the index u alone attains equality in item 3 → ∃ g : V^{r−1} → {0,1}^1 with error ≤ 1/(2(2^r − 1)) on every P and = 1/(2(2^r − 1)) on some P; reason: "attains equality in the max-bound" unfolded
--   - encoding: parties [r], index u ∈ V^{r−1} → Fin r counted from 0, Fin (r−1) → V; reason: relabelling
-- source:
--   Aggarwal, Secret Sharing Despite Non-Extractable Randomness, arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), Theorem 5.1, p.11 (PDF p.11); construction §5, displays (7), (8), p.10

import Mathlib
import Definitions.Def_SSNonExt_TV
import Definitions.Def_SSNonExt_IsPrivate
import Definitions.Def_SSNonExt_Supplement_shrR

namespace SSNonExt.Supplement

open SSNonExt

/-- **Theorem 5.1 (r-out-of-r).** "Let r ≥ 2 and b ≥ r. The scheme Π_b^{(r)} is a perfectly correct
r-out-of-r scheme for b-bit messages that is perfectly private for 𝒮_b^{(r)}, and: 1. each share has
b + 1 bits, and the key set 𝒦^{(r)} has (2^r − 1)2^{(r−1)b} elements; 2. every distribution in 𝒮_b^{(r)}
is uniform on a set of between (2^{r−1} − 1)N and 2^{r−1}N keys, and hence has min-entropy at least
(r − 1)b + log(2^{r−1} − 1); 3. for every ℓ ≥ 1 and every function Ext : 𝒦^{(r)} → {0, 1}^ℓ,
max_{P∈𝒮_b^{(r)}} TV(Ext(K), U_ℓ) ≥ 1/(2(2^r − 1)), K ∼ P; 4. for ℓ = 1, some function of the index u
alone attains equality in item 3."
D. Aggarwal, *Secret Sharing Despite Non-Extractable Randomness*, arXiv:2610.20173 (version of
2026-11-03, sha256 438a7f71…), Theorem 5.1, p.11 (PDF p.11); construction §5, displays (7), (8), p.10.

**Formalization Note.**
* Stated for **every** `γ_1, …, γ_r ∈ 𝔽_{2^b}` linearly independent over `𝔽₂ = ZMod 2`, the paper's
  "fix γ_1, …, γ_r ∈ V linearly independent over 𝔽₂".
* Correctness and privacy are Definition 2.1 with `t = r` (the full set reconstructs; the law of the
  shares of every set of fewer than `r` parties, the empty set included, does not depend on the
  message, `δ = 0`).
* `N = B^{r−1} = (2^b)^{r−1}`. Item 1: "b + 1 bits" is the size `2^{b+1}` of the share alphabet.
* Item 3: "max over 𝒮_b^{(r)} ≥ c" is "some `P` in the class has error ≥ c"; `{0,1}^ℓ` is `Fin ℓ → Bool`.
* Item 4: the error of `g ∘ index` (`index (u, S) = u`) is at most `1/(2(2^r − 1))` on every source of
  the class and equal to it on some source, with ℓ = 1.
* Logarithms are base 2. -/
theorem theorem_5_1 (b r : ℕ) (hr : 2 ≤ r) (hbr : r ≤ b) (γ : Fin r → V b)
    (hγ : LinearIndependent (ZMod 2) γ) :
    PerfectlyCorrect r (shrR (b := b) γ) ∧
      IsPrivate r 0 (srcClassR (b := b) hr) (shrR γ) ∧
      (Fintype.card (Share b) = 2 ^ (b + 1) ∧
        Fintype.card (KeyR b r) = (2 ^ r - 1) * 2 ^ ((r - 1) * b)) ∧
      (∀ P ∈ srcClassR (b := b) hr,
        (∃ (Z : Finset (KeyR b r)) (hZ : Z.Nonempty),
          P = PMF.uniformOfFinset Z hZ ∧ (2 ^ (r - 1) - 1) * (2 ^ b) ^ (r - 1) ≤ Z.card ∧
            Z.card ≤ 2 ^ (r - 1) * (2 ^ b) ^ (r - 1)) ∧
        (haveI := keyR_nonempty (b := b) hr;
          ((r : ℝ) - 1) * b + Real.logb 2 ((2 : ℝ) ^ (r - 1) - 1) ≤ minEntropy P)) ∧
      (∀ ℓ : ℕ, 1 ≤ ℓ → ∀ Ext : KeyR b r → (Fin ℓ → Bool),
        ∃ P ∈ srcClassR (b := b) hr,
          1 / (2 * ((2 : ℝ) ^ r - 1)) ≤ TV (P.map Ext) (PMF.uniformOfFintype (Fin ℓ → Bool))) ∧
      (∃ g : (Fin (r - 1) → V b) → (Fin 1 → Bool),
        (∀ P ∈ srcClassR (b := b) hr,
          TV (P.map (g ∘ keyIndexR)) (PMF.uniformOfFintype (Fin 1 → Bool)) ≤
            1 / (2 * ((2 : ℝ) ^ r - 1))) ∧
        (∃ P ∈ srcClassR (b := b) hr,
          TV (P.map (g ∘ keyIndexR)) (PMF.uniformOfFintype (Fin 1 → Bool)) =
            1 / (2 * ((2 : ℝ) ^ r - 1)))) := by sorry

end SSNonExt.Supplement
