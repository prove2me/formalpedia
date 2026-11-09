-- Prove2me | Theorems.Thm_SemAC02_theorem_4_16_size_bound
-- name    : SemAC02.theorem_4_16_size_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:30:19.912258+00:00
-- url     : https://prove2.me/theorems/499df5a3-e0fe-4d33-9b91-3a69c687c12c
-- title:
--   Theorem 4.16 — size bound via relative pseudo-reduction operators
-- statement:
--   Let $F$ be a family of circuits in $n$ variables and $S=\{[\![A]\!]:A\in F\}$. Fix $d\ge2$ and integers $r,R\ge1$ and $r^{d-1}\le k\le n$, and put
--   $$
--   q=Rr^{d-1},\qquad \alpha_j=\frac{H_n(k-r^{j-1})}{2H_n(k)},\qquad \theta=\min\{r\alpha_{d-1},R\alpha_d\}.
--   $$
--   Suppose $U\subseteq\mathcal B_n^{\le k}$ is a linear subspace such that every $0\ne f\in U$ has a non-zero $f$-relative pseudo-reduction of degree $3q$ for $S$. Then every depth-$d$ semantic AC0[2]-Frege refutation $\pi$ of $F$ satisfies
--   $$
--   \mathrm{size}(\pi)\ \ge\ \frac{\dim U}{H_n(k)}\,e^{\theta}. \tag{10}
--   $$
--
--   This is the abstract size lower bound: a large space of multipliers with non-vanishing relative pseudo-reductions forces large refutations.
--
--   Differences from the source:
--   - encoding: AC0[2] circuits with unordered children; size = number of distinct rooted subcircuits → Circ trees with List children; size = number of distinct subterms (proofSize / famSize); reason: a paper circuit is a list presentation of itself with the same evaluation, depth and size; normalising a list circuit or refutation never increases depth or the distinct-subterm count; same instances
--   - encoding: a non-zero linear map into any linear space W → HasNonzeroRelPseudoRed: some W : Type with AddCommGroup and Module (ZMod 2); reason: a non-zero operator into any W gives one onto its image, which can be taken in Type; same instances
--   - encoding: dim(U) → Module.finrank (ZMod 2) U; reason: U is finite-dimensional
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Theorem 4.16, p.36 (PDF p.38)

import Mathlib
import Definitions.Def_SemAC02_Circ
import Definitions.Def_SemAC02_IsSemRefutation
import Definitions.Def_SemAC02_arith
import Definitions.Def_SemAC02_Ble
import Definitions.Def_SemAC02_IsRelPseudoRed

namespace SemAC02

/-- **Theorem 4.16 (Size bound via relative pseudo-reduction operators)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission),
Theorem 4.16, p.36): let `F` be a family of circuits in `n` variables, and put
`S = {⟦A⟧ : A ∈ F}`. Fix `d ≥ 2`, integers `r, R ≥ 1` and `r^{d−1} ≤ k ≤ n`, and put
`q = R r^{d−1}`, `α_j = H_n(k − r^{j−1})/(2H_n(k))`, `θ = min{r α_{d−1}, R α_d}`. Suppose
`U ⊆ B_n^{≤k}` is a linear subspace such that, for every `0 ≠ f ∈ U`, there is a non-zero
`f`-relative pseudo-reduction of degree `3q` for `S`. Then every depth-`d` semantic
AC0[2]-Frege refutation `π` of `F` satisfies `size(π) ≥ (dim(U)/H_n(k)) exp(θ)` (10).

**Formalization Note** `dim` is `Module.finrank`; the pseudo-reduction may take values in any
`𝔽₂`-vector space `W : Type` (`HasNonzeroRelPseudoRed`). `size(π)` is `proofSize π`. -/
theorem theorem_4_16_size_bound {n : ℕ} (F : Set (Circ (Fin n))) (d r R k : ℕ) (hd : 2 ≤ d)
    (hr : 1 ≤ r) (hR : 1 ≤ R) (hrk : r ^ (d - 1) ≤ k) (hkn : k ≤ n)
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))) (hU : U ≤ Ble (Fin n) k)
    (hred : ∀ f ∈ U, f ≠ 0 → HasNonzeroRelPseudoRed (arith '' F) f (3 * (R * r ^ (d - 1))))
    (π : List (Circ (Fin n))) (hπ : IsSemRefutation d F π) :
    (Module.finrank (ZMod 2) U : ℝ) / (Hn n k : ℝ) *
        Real.exp (min ((r : ℝ) * ((Hn n (k - r ^ (d - 2)) : ℝ) / (2 * (Hn n k : ℝ))))
          ((R : ℝ) * ((Hn n (k - r ^ (d - 1)) : ℝ) / (2 * (Hn n k : ℝ))))) ≤
      (proofSize π : ℝ) := by sorry

end SemAC02
