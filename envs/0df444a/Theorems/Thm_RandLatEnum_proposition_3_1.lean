-- Prove2me | Theorems.Thm_RandLatEnum_proposition_3_1
-- name    : RandLatEnum.proposition_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:15:21.274384+00:00
-- url     : https://prove2.me/theorems/befb5af2-2846-4e10-ae9d-8e88f90e977e
-- title:
--   Proposition 3.1 — $\ln T(B)=\max_kP_k(B)+O(n)$ and $\ln N_{n-k}=P_k+O(n)$ for all bases, w.p. $1-e^{-\Omega(n)}$
-- statement:
--   Let $L\sim\mu_n$ and $R=\lambda_1(L)$. With probability $1-e^{-\Omega(n)}$, simultaneously for all bases $B$ of $L$,
--   $$
--   \ln T(B)=\max_{0\le k\le n}P_k(B)+O(n),\qquad \ln N_{n-k}(B,R)=P_k(B)+O(n)\quad(0\le k<n).
--   $$
--   Here the constant in $O(n)$ and the rate in $\Omega(n)$ are absolute: there are $C>0$ and $\kappa>0$ such that, for all large $n$, the probability that some basis violates $|\ln T(B)-\max_kP_k(B)|\le Cn$ or some $|\ln N_{n-k}(B,R)-P_k(B)|\le Cn$ is at most $e^{-\kappa n}$.
--
--   This reduces tree sizes to prefix profiles, uniformly over all bases.
--
--   **Formalization Note** $N_{n-k}(B,R)$ is the level count with 0-based projection index $k$.
--
--   Differences from the source:
--   - encoding: the Haar probability measure µ_n on X_n → any SL_n(ℝ)-invariant Borel probability measure on X_n, taken as a hypothesis; reason: X_n has exactly one such measure (Siegel), so the instances are the same; Mathlib does not construct it
--   - encoding: the probability of an event → the measure of the set, i.e. its outer measure; reason: the paper assumes all choices measurable (p.14); for a measurable set the two agree, and the outer measure is the stronger reading
--   - reading: O(n) and e^{−Ω(n)} → one absolute constant C > 0 and one absolute rate κ > 0, independent of the lattice, the basis and n; reason: the proof gives such constants ((3.4)–(3.5)); a constant depending on the basis would not make the statement uniform as printed
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), Proposition 3.1, (3.3), p.17

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_RandLatEnum_X
import Definitions.Def_RandLatEnum_latticeOf
import Definitions.Def_RandLatEnum_IsHaarLatticeMeasure
import Definitions.Def_RandLatEnum_prefixLogDet
import Definitions.Def_RandLatEnum_maxPrefixLogDet
import Definitions.Def_RandLatEnum_levelCount
import Definitions.Def_RandLatEnum_treeSize

namespace RandLatEnum

open MeasureTheory Filter KannanLattice.Core

/-- **Proposition 3.1 (Tree size from the prefix profile)** (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), Proposition 3.1, (3.3), p.17).
With probability `1 − e^{−Ω(n)}` over `L ∼ µ_n`, simultaneously for all bases at radius
`R = λ₁(L)`, `ln T(B) = max_{0≤k≤n} P_k(B) + O(n)` and `ln N_{n−k}(B, R) = P_k(B) + O(n)` (`k < n`).

**Formalization Note.** `O(n)` is one absolute constant `C` and `Ω(n)` one absolute rate `κ > 0`,
independent of the lattice and the basis. `N_{n−k}(B, R)` is `levelCount b k R` (projection index
`k`, 0-based). The bad set (some basis violating an estimate) has outer measure `≤ e^{−κn}` for all
large `n`. -/
theorem proposition_3_1 (μ : ∀ n : ℕ, Measure (X n)) (hμ : ∀ n, IsHaarLatticeMeasure (μ n)) :
    ∃ C : ℝ, 0 < C ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
      μ n {x : X n | ∃ B : Module.Basis (Fin n) ℤ (latticeOf x),
          ¬ (|Real.log (treeSize (fun i => (B i : EuclideanSpace ℝ (Fin n)))
                  (lambdaOne (latticeOf x : Set (EuclideanSpace ℝ (Fin n))))) -
                maxPrefixLogDet (fun i => (B i : EuclideanSpace ℝ (Fin n)))| ≤ C * n ∧
             ∀ k : Fin n,
              |Real.log (levelCount (fun i => (B i : EuclideanSpace ℝ (Fin n))) k
                  (lambdaOne (latticeOf x : Set (EuclideanSpace ℝ (Fin n))))) -
                prefixLogDet (fun i => (B i : EuclideanSpace ℝ (Fin n))) k| ≤ C * n)} ≤
        ENNReal.ofReal (Real.exp (-κ * n)) := by sorry

end RandLatEnum
