-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_certifiedIncompatibility
-- name    : QAlgorithms.Papers.Independent.Information100.P44.certifiedIncompatibility
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:27:36.96262+00:00
-- url     : https://prove2.me/theorems/02073bb5-f4a8-44fa-a915-1bb2163003cb
-- title:
--   Paper seed / Theorem 5: certified incompatibility of three CGP-optimal directional transfers
-- statement:
--   Fix the energy eigenbasis $(|0\rangle,|1a\rangle,|1b\rangle,|3\rangle)$, Hamiltonian $H=\operatorname{diag}(0,1,1,3)$, inverse temperature $\beta=1$, and Gibbs state $\gamma=\operatorname{diag}(1,e^{-1},e^{-1},e^{-3})/(1+2e^{-1}+e^{-3})$. The input is
--   $$\rho=\frac1{100}\begin{pmatrix}35&5&0&4\\5&25&0&0\\0&0&20&5\\4&0&5&20\end{pmatrix}.$$
--   Let $\Gamma_{\rm CGP}$ be the CPTP, time-translation covariant, Gibbs-preserving channels whose output on $\rho$ has total energy populations $(1/2,7/20,3/20)$. The two populations at energy $1$ are constrained only through their sum. For such channels define $(L_1,L_2,L_3)(\Phi)=(\operatorname{Re}\Phi(\rho)_{01},\operatorname{Re}\Phi(\rho)_{23},\operatorname{Re}\Phi(\rho)_{03})$ and $L_k^\star=\sup_{\Phi\in\Gamma_{\rm CGP}}L_k(\Phi)$. Then
--   $$\nexists\Phi\in\Gamma_{\rm CGP}\quad\forall k\in\{1,2,3\},\ L_k(\Phi)=L_k^\star.$$
--   No finite-bath thermal operation satisfying the same output-population constraints attains this triple either. This is an incompatibility of the three CGP-optimal directional values; it makes no assertion that any individual CGP optimum is attainable by a thermal operation.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 18, Paper seed / Theorem 5: certified incompatibility of three CGP-optimal directional transfers

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF pp.18–19, Theorem 5 (the p.1 paper seed): neither CGP nor finite TO attain
all three individual CGP-optimal signed directional values. -/
theorem certifiedIncompatibility :
    (¬ ∃ Phi : Map 4, FixedChannelFeasible Phi ∧
      ∀ k : Fin 3, channelObjective k Phi = cgpOptimum k) ∧
    (¬ ∃ Phi : Map 4, FixedTOFeasible Phi ∧
      ∀ k : Fin 3, channelObjective k Phi = cgpOptimum k) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
