-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_dickeSchmidt
-- name    : QAlgorithms.Papers.Independent.Information100.P22.dickeSchmidt
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:14:46.608603+00:00
-- url     : https://prove2.me/theorems/bb158a3d-7917-45dd-9853-d0cc9b8f7a4d
-- title:
--   Eqs.(S67)–(S68), unnumbered: balanced Dicke Schmidt decomposition
-- statement:
--   Let $\nu\ge1$ and $0\le r\le2\nu$. Put $j_-=\max(0,r-\nu)$, $j_+=\min(r,\nu)$ and $\lambda_j=\binom\nu j\binom\nu{r-j}/\binom{2\nu}r$. Across a balanced cut,
--   $$|D_{2\nu}^{(r)}\rangle=\sum_{j=j_-}^{j_+}\sqrt{\lambda_j}|D_\nu^{(j)}\rangle|D_\nu^{(r-j)}\rangle.$$
--   All the displayed Dicke vectors are normalized; distinct feasible indices give orthogonal vectors on both sides. The reduced rank is $j_+-j_-+1\le\nu+1$ and its bit entropy equals $-\sum_j\lambda_j\log_2\lambda_j\le\log_2(\nu+1)$. Product endpoints are included. This supplies exact Schmidt probabilities and the entropy bound.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 43, Eqs.(S67)–(S68), unnumbered: balanced Dicke Schmidt decomposition

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- Eqs.(S67)–(S68), PDF pp.42–43. Feasible interval protects the natural subtraction r-j. -/
theorem dickeSchmidt (nu r : ℕ) (hnu : 1 ≤ nu) (hr : r ≤ 2*nu) :
    dickeResource (Fin nu) r =
      ∑ j ∈ Finset.Icc (r-nu) (min r nu), (Real.sqrt (dickeLambda nu r j) : ℂ) •
        tensorVec (dicke (I := Fin nu) j) (dicke (I := Fin nu) (r-j)) ∧
    (∀ j ∈ Finset.Icc (r-nu) (min r nu), IsState (dicke (I := Fin nu) j) ∧
      IsState (dicke (I := Fin nu) (r-j))) ∧
    (∀ j ∈ Finset.Icc (r-nu) (min r nu), ∀ l ∈ Finset.Icc (r-nu) (min r nu), j ≠ l →
      inner ℂ (dicke (I := Fin nu) j) (dicke (I := Fin nu) l) = 0 ∧
      inner ℂ (dicke (I := Fin nu) (r-j)) (dicke (I := Fin nu) (r-l)) = 0) ∧
    (traceRight (pureDensity (dickeResource (Fin nu) r))).rank = min r nu-(r-nu)+1 ∧
    (traceRight (pureDensity (dickeResource (Fin nu) r))).rank ≤ nu+1 ∧
    vnEntropy (traceRight (pureDensity (dickeResource (Fin nu) r))) = dickeEntropy nu r ∧
    dickeEntropy nu r ≤ Real.logb 2 (nu+1) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
