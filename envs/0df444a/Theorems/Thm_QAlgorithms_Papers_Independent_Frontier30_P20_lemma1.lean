-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P20_lemma1
-- name    : QAlgorithms.Papers.Independent.Frontier30.P20.lemma1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:31:25.61799+00:00
-- url     : https://prove2.me/theorems/b07daba5-7aae-489b-9ac7-351c464b337a
-- title:
--   Lemma 1 (Markovian approximation)
-- statement:
--   All maps act complex-linearly on the same matrix algebra $M_d(\mathbb C)$, where $d\ge1$. Composition $AB$ applies $B$ first. Norms of maps are induced by the unnormalized Hilbert–Schmidt norm. For every CPTP map $T$,
--
--   $$e^{t(T-\mathrm{id})}\text{ is CPTP for every }t\ge0.$$
--
--   If the unitary conjugation $U_0$ maximizes the superoperator trace $\operatorname{tr}_{\mathcal H}(TU)$ among unitary conjugations $U$, then $TU_0-\mathrm{id}$ also generates a CPTP semigroup and is purely dissipative. Here pure dissipation means zero Hamiltonian in a traceless Hilbert–Schmidt orthonormal Lindblad representation.
--
--   This assigns a canonical dissipative Markovian approximation to a channel.
-- source:
--   Dividing Quantum Channels, arXiv:math-ph/0611057v3, PDF p. 5, Lemma 1 (Markovian approximation)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P20

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P20

open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer)

open QAlgorithms.Papers.Independent.Dependency50.P14 (Super)

-- Accepted matrix-unit coordinates on the action of a superoperator.

local notation "coefficients" =>
  QAlgorithms.Papers.Independent.Dependency50.P12.superOfAction

/-- Lemma 1, PDF p.5: Markovian approximation and canonical pure dissipation. -/
theorem lemma1 {d : ℕ} (hd : 0 < d) (T : Super d) (hT : Channel T) :
    IsGenerator (T - 1) ∧
    (∀ U : Super d, Maximizer T U →
      IsGenerator (T * U - 1) ∧ PurelyDissipative (T * U - 1)) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P20

end
