-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P33_honest_encoding
-- name    : QAlgorithms.Papers.Independent.Advance50.P33.honest_encoding
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:30:31.101581+00:00
-- url     : https://prove2.me/theorems/a98d49df-efb3-42e0-9d66-e4ffeb293f5a
-- title:
--   Normalized orthogonal encodings and perfect honest parity unveiling
-- statement:
--   Work in the full two-mode bosonic Fock space, with token first and proof second, ideal readout, and a lossless balanced interferometer with matched delays. Let $a\in\mathbb C\setminus\{0\}$, $s_b=2b-1$, and let $|a\rangle$ be the normalized coherent state. Define
--   $$
--   |\chi_b(a)\rangle=\frac{|a,-a\rangle+s_b|-a,a\rangle}{\sqrt{2(1+s_b e^{-4|a|^2})}},\qquad
--   |c_b(A)\rangle=\frac{|A\rangle+s_b|-A\rangle}{\sqrt{2(1+s_b e^{-2|A|^2})}}.
--   $$
--   A unitary balanced beam splitter $B$ exists with coherent amplitude action $(z,w)\mapsto((z-w)/\sqrt2,(z+w)/\sqrt2)$. Both encodings and both corresponding cats are unit vectors, the encodings are orthogonal, and the fixed $B$ satisfies
--   $$
--   B|\chi_b(a)\rangle=|c_b(\sqrt2a)\rangle\otimes|0\rangle,\qquad
--   \langle P\otimes I\rangle_{B\chi_0}=-1,\quad \langle P\otimes I\rangle_{B\chi_1}=1.
--   $$
--   Here $P=(-1)^{\hat n}$ is photon parity. Thus the ideal honest unveiling is perfect. These identities do not assert exact concealment of the token.
-- source:
--   Quantum bit commitment under Gaussian constraints, arXiv:1105.2140v2, PDF p. 2, II, Eqs.(3)–(5): normalized orthogonal encodings and perfect honest unveiling

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P33

open Filter

open scoped BigOperators Topology

open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator BipartiteFock fockKet bipartiteKet coherentKet
   coherentCoefficient CoherentRealized displacement displacementMatrix
   DisplacementRealized HasFockMatrix operatorOfMatrix IsDensity IsTraceClass
   nuclearTraceNorm fockTrace)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.2--3, Eqs.(3)--(5): normalized orthogonal encodings, their exact
balanced-interferometer outputs, and both honest parity signs. Nonzero a avoids
the undefined odd-cat normalization; no claim of exact concealment is made. -/
theorem honest_encoding :
    CoherentRealized ∧
    IsBalanced balancedInterferometer ∧
    ∀ (a : ℂ), a ≠ 0 →
      (∀ b : Bool, ‖commitmentEncoding a b‖ = 1 ∧ ‖cat ((Real.sqrt 2 : ℂ) * a) b‖ = 1) ∧
      inner ℂ (commitmentEncoding a false) (commitmentEncoding a true) = 0 ∧
      (∀ b : Bool, balancedInterferometer (commitmentEncoding a b) =
        fockTensorPair (cat ((Real.sqrt 2 : ℂ) * a) b) (fockKet 0)) ∧
      firstParity (balancedInterferometer (commitmentEncoding a false)) = -1 ∧
      firstParity (balancedInterferometer (commitmentEncoding a true)) = 1 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P33

end
