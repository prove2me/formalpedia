-- Prove2me | Theorems.Thm_PauliUnclonable531_Pauli_ricochet
-- name    : PauliUnclonable531.Pauli.ricochet
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:42.380659+00:00
-- url     : https://prove2.me/theorems/76616129-7086-4e4b-ba3b-053e13242e9a
-- title:
--   Section 4.1, Eq. (22) — success probability and largest eigenvalue
-- statement:
--   For every n≥1 and admissible pre-key splitting attack with arbitrary nonzero finite output registers B,C, form the normalized Choi state τ. The local POVM differences Bₖ=Λᴷ_B,0−Λᴷ_B,1 and Cₖ=Λᴷ_C,0−Λᴷ_C,1 form admissible Hermitian-contraction decoder families, τ is a density operator, and
--
--   $$p=\frac{1+\operatorname{Tr}(G\tau)}2\le\frac{1+\lambda_{\max}(G)}2.$$
--
--   Here p is the actual fixed-(0,1) Born winning probability and G is computed from those decoder families, rather than chosen arbitrarily. The existential decoder witness only packages the proved validity of the displayed POVM differences. This is the source's game reduction, with its normalization and transpose convention intact.
--
--   Differences from the source:
--   - encoding: finite-dimensional complex Hilbert-space operators and binary strings → complex matrices indexed by finite computational bases, Fin 2 bits, real Born probabilities, Euclidean spectral norm and PSD-difference order; reason: these are the same finite-dimensional objects and conventions after choosing the source basis
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026), §4.1, p.18, Eqs. (18)–(22)

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Correlations

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

/-- §4.1, Eqs. (18)–(22), p.18. Validity of the decoding observables and Choi state
is concluded here, never assumed as security-bearing structure fields. -/
theorem ricochet {B C : Type} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    [Nonempty B] [Nonempty C] (n : ℕ) (hn : 1 ≤ n) (a : Attack n B C) :
    ∃ d : Decoders n B C,
      (∀ k, d.bob k = bobEffect a k 0 - bobEffect a k 1) ∧
      (∀ k, d.charlie k = charlieEffect a k 0 - charlieEffect a k 1) ∧
      Density (choi a.split) ∧
      win a = (1 + born (gameOperator d) (choi a.split)) / 2 ∧
      win a ≤ (1 + largestEigenvalue (gameOperator d)) / 2 := by sorry

end PauliUnclonable531.Pauli
