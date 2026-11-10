-- Prove2me | Theorems.Thm_RandomDimReduction_Channel_lemma_2_3
-- name    : RandomDimReduction.Channel.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:25:19.286951+00:00
-- url     : https://prove2.me/theorems/dfb691ab-cc0a-450c-83a8-8694699ba69b
-- title:
--   Lemma 2.3 — the moment commutes with permutations
-- statement:
--   For positive $n,k,d$ with $k\le d$ and every permutation $\pi\in S_n$, the Grassmannian moment satisfies
--   $$ M_{k\hookrightarrow d}^{(n)}F_\pi^d=F_\pi^dM_{k\hookrightarrow d}^{(n)}. $$
--   The permutation convention sends a basis word $i$ to $i\circ\pi^{-1}$. This is the symmetry of the moment used throughout the reduction statements.
--
--   Differences from the source:
--   - encoding: finite-dimensional tensor Hilbert spaces and complex linear operators → matrices on Fin n → Fin d, with zero-based coordinates; reason: standard orthonormal coordinates preserve every operator and isometry
--   - encoding: the commutator [M,Fπ] is zero → M Fπ = Fπ M; reason: these are identical commutation conditions
-- source:
--   Angus Lowe, Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), Lemma 2.3, p.7. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf

import Definitions.Def_RandomDimReduction_Channel_Moment
import Definitions.Def_RandomDimReduction_Channel_Schur

set_option autoImplicit false

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise ENNReal

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 2.3, p.7: M commutes with every tensor permutation. -/
theorem lemma_2_3 (n k d : ℕ) (hn : 0 < n) (hk : 1 ≤ k) (hkd : k ≤ d)
    (π : Equiv.Perm (Fin n)) :
    moment n k d * QAlgorithms.Schur.tensorPermutation d n π =
      QAlgorithms.Schur.tensorPermutation d n π * moment n k d := by sorry

end RandomDimReduction.Channel
