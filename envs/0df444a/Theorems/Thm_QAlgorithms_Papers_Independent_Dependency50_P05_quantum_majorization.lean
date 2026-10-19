-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P05_quantum_majorization
-- name    : QAlgorithms.Papers.Independent.Dependency50.P05.quantum_majorization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:01:06.154732+00:00
-- url     : https://prove2.me/theorems/94888c3a-9305-40f6-9e0e-0dcc85ad0da5
-- title:
--   Quantum majorization of channels by all paired entropy tests
-- statement:
--   All systems are finite dimensional complex Hilbert spaces with strictly positive input and output dimensions. A system $A$ comprises $A_0,A_1$. Channels are complex-linear CPTP maps on all operators, and a superchannel is completely CP-preserving and trace-preserving-map preserving. Its complete extension includes both registers of every auxiliary dynamical system. Write $J_\Theta$ for the unnormalized, input-first supermap Choi matrix, $J^S$ for its ordinary partial-trace marginal, and $u^S=I^S/d_S$. Tensor formulas use the named register order. Let $\Phi^{RA},\Psi^{RB}$ be bipartite channels. Fix $d_X=d_{R_0}^2$ normalized rank-one input projectors spanning the Hermitian operators of $R_0$, and an informationally complete basis POVM with $d_Y=d_{R_1}^2$ outcomes on $R_1$. Preparing probe $x$ and observing outcome $y$ gives CP instrument branches $\Phi_{y|x}^A,\Psi_{y|x}^B$. For every family of CP maps $\Lambda_{y|x}^B$ whose sum over $y$ is CPTP for each $x$, form
--   $$\Lambda_\Phi=\frac1{d_X}\sum_{x,y}\Phi_{y|x}^A\otimes\Lambda_{y|x}^B,\qquad\Lambda_\Psi=\frac1{d_X}\sum_{x,y}\Psi_{y|x}^{\widetilde B}\otimes\Lambda_{y|x}^B.$$
--   Then a superchannel $\Theta:A\to B$ satisfying $(1^R\otimes\Theta)[\Phi]=\Psi$ exists if and only if, for every such test instrument,
--   $$H_{\min}^{\rm ext}(B|A)_{\Lambda_\Phi}\le H_{\min}^{\rm ext}(B|\widetilde B)_{\Lambda_\Psi}.$$
--   Here $\widetilde B$ is a fixed-basis identical copy of $B$. The paired maps need only be CP and may vanish. Their entropy is defined by the same homogeneous primal problem using $J/(d_{\rm input})$, with zero assigned $+\infty$; they are never divided by their trace. This is the full channel comparison theorem.
-- source:
--   Comparison of Quantum Channels by Superchannels, arXiv:1808.02607v3, PDF p. 18, Theorem 7, continued p.19

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P05

local notation "Mat" I:max => Matrix I I ℂ

/-- arXiv:1808.02607v3, PDF pp.18–20, Theorem 7: full channel quantum-majorization criterion.
The paired maps are merely CP; Definition 4 is extended homogeneously, including zero.
The input tomography has d_R0^2 probes and the POVM has exactly d_R1^2 outcomes. -/
theorem quantum_majorization (A B R : System)
    (F : Mat (ChoiRegister A × ChoiRegister R)) (G : Mat (ChoiRegister B × ChoiRegister R))
    (hF : BipartiteChannel A R F) (hG : BipartiteChannel B R G) (t : Tomography R) :
    QuantumMajorizes F G ↔
      ∀ K : Fin (R.input ^ 2) → Fin (R.output ^ 2) → Mat (ChoiRegister B),
        InstrumentFamily B (R.input ^ 2) (R.output ^ 2) K →
        extendedConditional A B (pairedMap (extractedBranch F t) K) ≤
          extendedConditional B B (pairedMap (extractedBranch G t) K) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P05

end
