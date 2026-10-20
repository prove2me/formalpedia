-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_monotonicity_implication_diagram
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.monotonicity_implication_diagram
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:12:19.082101+00:00
-- url     : https://prove2.me/theorems/db44bd05-4206-4272-b5b4-8962482dd1bc
-- title:
--   The appendix monotonicity implication diagram
-- statement:
--   For an arbitrary divergence family D on state pairs over all finite dimensions, SMON denotes monotonicity under stochastic maps in the stated Schwarz/co-Schwarz sense; EPPMON denotes tensor-stable positive TP monotonicity; MON, MMON and PMON denote CPTP, commuting-range measurement, and reference-pinching monotonicity. The implications are
--
--   A stochastic map is a convex combination of two TP maps whose Hilbert–Schmidt adjoints are respectively Schwarz and Schwarz composed with a transpose in some orthonormal basis. A Schwarz map $\Psi$ satisfies $\Psi(X)^*\Psi(X)\leq\Psi(X^*X)$ for every matrix $X$. Every map in the monotonicity classes is complex-linear, positive, and trace preserving.
--
--   $$
--   \mathrm{SMON}\Rightarrow\mathrm{MON},\quad\mathrm{EPPMON}\Rightarrow\mathrm{MON},\quad\mathrm{MON}\Rightarrow\mathrm{MMON}\Rightarrow\mathrm{PMON}.
--   $$
--
--   The diagram organizes the source’s different monotonicity requirements.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 21, The following implications are obvious:

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P28

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support positivePart positiveProjection)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:1309.3228v5, PDF p.21: The appendix monotonicity implication diagram. Both vertical arrows point INTO MON. A pinching need not have commuting full range: MMON→PMON uses a pair-dependent common-eigenbasis measurement giving the same pinched pair. No additivity assumption is supplied. -/
theorem monotonicity_implication_diagram (d : Divergence) :
    (SMON d → MON d) ∧ (EPPMON d → MON d) ∧
    (MON d → MMON d) ∧ (MMON d → PMON d) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
