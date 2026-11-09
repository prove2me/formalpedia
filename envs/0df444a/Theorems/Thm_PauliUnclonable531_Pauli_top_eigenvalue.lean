-- Prove2me | Theorems.Thm_PauliUnclonable531_Pauli_top_eigenvalue
-- name    : PauliUnclonable531.Pauli.top_eigenvalue
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:59.599226+00:00
-- url     : https://prove2.me/theorems/29d3fd40-d49f-49b2-91da-b2235dc629cc
-- title:
--   Lemma 4.9 — positive largest eigenvalue estimate
-- statement:
--   Let n≥1, d=2ⁿ and K=4ⁿ−1. On arbitrary nonzero finite complex registers B,C choose key-indexed Hermitian contractions Bₖ,Cₖ. Set Θₖ=Pₖᵀ and define E_B,E_C,E_BC,D and G by Definition 4.3: E_B and E_C average the reference–receiver tensors, E_BC averages I⊗Bₖ⊗Cₖ, D=I−E_BC, and G=(E_B+E_C−D)/2. Write γ=d/K.
--
--   $$t^2\le\|E_BF(t)E_C\|_\infty,\qquad t=\lambda_{\max}(G)>0.$$
--
--   The largest eigenvalue retains its sign; it is not the operator norm of G. The other branch remains available in the final security theorem.
--
--   Differences from the source:
--   - encoding: finite-dimensional complex Hilbert-space operators and binary strings → complex matrices indexed by finite computational bases, Fin 2 bits, real Born probabilities, Euclidean spectral norm and PSD-difference order; reason: these are the same finite-dimensional objects and conventions after choosing the source basis
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026), Lemma 4.9, p.24

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Correlations

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

theorem top_eigenvalue {B C : Type} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    [Nonempty B] [Nonempty C] (n : ℕ) (hn : 1 ≤ n) (a : Decoders n B C) (ht : 0 < largestEigenvalue (gameOperator a)) :
    (largestEigenvalue (gameOperator a))^2 ≤
      spectralNorm (EB a * filterOperator a (largestEigenvalue (gameOperator a)) * EC a) := by sorry

end PauliUnclonable531.Pauli
