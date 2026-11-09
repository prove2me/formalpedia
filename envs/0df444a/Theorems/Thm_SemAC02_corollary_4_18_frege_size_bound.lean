-- Prove2me | Theorems.Thm_SemAC02_corollary_4_18_frege_size_bound
-- name    : SemAC02.corollary_4_18_frege_size_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:30:03.286364+00:00
-- url     : https://prove2.me/theorems/08a4f7e4-4bb9-4c85-8c36-3bfe804db893
-- title:
--   Corollary 4.18 — size bound for semantic AC0[2]-Frege
-- statement:
--   Let $F$ be a family of AC0[2] circuits in $n$ variables and $S=\{[\![A]\!]:A\in F\}$. Fix integers $d\ge2$, $r,R\ge1$ and $0<\epsilon\le1/256$, and put
--   $$
--   k=\lfloor(1/2-\epsilon)n\rfloor,\qquad q=Rr^{d-1},\qquad \theta=\tfrac12\min\bigl\{r\,e^{-128\epsilon r^{d-2}},\ R\,e^{-128\epsilon r^{d-1}}\bigr\}.
--   $$
--   Suppose $n\ge16/\epsilon^2$, $r^{d-1}\le\epsilon n/2$, and $U\subseteq\mathcal B_n^{\le k}$ is a linear subspace such that every $0\ne f\in U$ has a non-zero degree-$3q$ $f$-relative pseudo-reduction operator for $S$. Then every semantic depth-$d$ AC0[2]-Frege refutation $\pi$ of $F$ satisfies
--   $$
--   \mathrm{size}(\pi)\ \ge\ \frac{\dim U}{H_n(k)}\,e^{\theta}. \tag{12}
--   $$
--
--   The corollary makes the exponent of Theorem 4.16 explicit for a degree cutoff slightly below $n/2$.
--
--   Differences from the source:
--   - encoding: AC0[2] circuits with unordered children; size = number of distinct rooted subcircuits → Circ trees with List children; size = number of distinct subterms (proofSize / famSize); reason: a paper circuit is a list presentation of itself with the same evaluation, depth and size; normalising a list circuit or refutation never increases depth or the distinct-subterm count; same instances
--   - encoding: a non-zero operator into any linear space W → HasNonzeroRelPseudoRed (some W : Type); reason: a non-zero operator into any W gives one onto its image; same instances
--   - encoding: k := ⌊(1/2 − ε)n⌋ → Nat.floor ((1/2 − ε) * n); reason: k ≥ 0 since ε ≤ 1/256
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Corollary 4.18, p.37 (PDF p.39)

import Mathlib
import Definitions.Def_SemAC02_Circ
import Definitions.Def_SemAC02_IsSemRefutation
import Definitions.Def_SemAC02_arith
import Definitions.Def_SemAC02_Ble
import Definitions.Def_SemAC02_IsRelPseudoRed

namespace SemAC02

/-- **Corollary 4.18 (Size bound for semantic AC0[2]-Frege)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission), Corollary 4.18,
p.37): let `F` be a family of AC0[2] circuits in `n` variables, and let `S = {⟦A⟧ : A ∈ F}` be
its arithmetisation. Fix integers `d ≥ 2` and `r, R ≥ 1`, and a parameter `0 < ϵ ≤ 1/256`, and
put `k := ⌊(1/2 − ϵ)n⌋`, `q := R r^{d−1}`,
`θ := (1/2) min{r e^{−128ϵ r^{d−2}}, R e^{−128ϵ r^{d−1}}}`. Suppose that `n ≥ 16/ϵ²`,
`r^{d−1} ≤ ϵn/2`, and that `U ⊆ B_n^{≤k}` is a linear subspace such that, for every `0 ≠ f ∈ U`,
there is a non-zero degree-`3q` `f`-relative pseudo-reduction operator for `S`. Then every
semantic depth-`d` AC0[2]-Frege refutation `π` of `F` satisfies
`size(π) ≥ (dim(U)/H_n(k)) exp(θ)` (12).

**Formalization Note** `k` is `Nat.floor ((1/2 − ϵ) n)`. The pseudo-reduction may take values in
any `𝔽₂`-vector space `W : Type`. `size(π)` is `proofSize π`. -/
theorem corollary_4_18_frege_size_bound {n : ℕ} (F : Set (Circ (Fin n))) (d r R : ℕ) (hd : 2 ≤ d)
    (hr : 1 ≤ r) (hR : 1 ≤ R) (ε : ℝ) (hε₀ : 0 < ε) (hε : ε ≤ 1 / 256)
    (hn : 16 / ε ^ 2 ≤ (n : ℝ)) (hrn : (r : ℝ) ^ (d - 1) ≤ ε * n / 2)
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (hU : U ≤ Ble (Fin n) ⌊(1 / 2 - ε) * (n : ℝ)⌋₊)
    (hred : ∀ f ∈ U, f ≠ 0 → HasNonzeroRelPseudoRed (arith '' F) f (3 * (R * r ^ (d - 1))))
    (π : List (Circ (Fin n))) (hπ : IsSemRefutation d F π) :
    (Module.finrank (ZMod 2) U : ℝ) / (Hn n ⌊(1 / 2 - ε) * (n : ℝ)⌋₊ : ℝ) *
        Real.exp (1 / 2 * min ((r : ℝ) * Real.exp (-(128 * ε * (r : ℝ) ^ (d - 2))))
          ((R : ℝ) * Real.exp (-(128 * ε * (r : ℝ) ^ (d - 1))))) ≤
      (proofSize π : ℝ) := by sorry

end SemAC02
