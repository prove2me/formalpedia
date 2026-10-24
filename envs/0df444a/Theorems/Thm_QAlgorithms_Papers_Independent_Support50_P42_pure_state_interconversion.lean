-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P42_pure_state_interconversion
-- name    : QAlgorithms.Papers.Independent.Support50.P42.pure_state_interconversion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:23:59.572402+00:00
-- url     : https://prove2.me/theorems/0771bf9a-7132-43c1-a8d7-fdc7a5c9d112
-- title:
--   Asymptotically reversible conversion of pure states
-- statement:
--   Let $\psi$ and $\phi$ be normalized shared pure states on positive finite local dimensions. Call $R$ achievable if, for every error and rate slack, all sufficiently large numbers $n$ of input copies admit finite local protocols producing $m$ target copies with vanishing global error and $m/n\ge R$ up to that slack. If $E(\phi)>0$, then
--
--   $$R\text{ is achievable}\quad\Longleftrightarrow\quad 0\le R\le\frac{E(\psi)}{E(\phi)}.$$
--
--   If $E(\phi)=0$, every nonnegative rate is achievable by local preparation. Thus equal positive entropies permit unit-rate interconversion, while a product input cannot achieve a positive rate to an entangled target. The source's printed reciprocal ratio is interpreted as input cost; the displayed ratio counts output copies per input copy.
-- source:
--   Concentrating Partial Entanglement by Local Operations, arXiv:quant-ph/9511030v1, PDF p. 16, §V: asymptotically reversible pure-state conversion

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P42

open scoped BigOperators Matrix ComplexConjugate

open MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact accepted objects, without introducing same-name aliases.

open Information100.P21 (Op Vec FiniteLOCC)

open Dependency50.P42 (dimensionedPower singlets)

open Dependency50.P48 (pureFidelity)

open Gap48.P32 (pairOfState)

open Next46.P39 (rectAct)

/-- PDF p.16: full pure-state conversion rates. The printed reciprocal yield
is corrected to E(input)/E(output) for output dimensionedPower per input copy, as fixed
by concentration and dilution. Product targets require only local preparation. -/
theorem pure_state_interconversion (s t : Shared) (hs : IsPureShared s) (ht : IsPureShared t) :
    (0<ent t → ∀ R : ℝ, ConversionRate s t R ↔ 0≤R ∧ R≤ent s/ent t) ∧
    (ent t=0 → ∀ R : ℝ, 0≤R → ConversionRate s t R) := by sorry

end QAlgorithms.Papers.Independent.Support50.P42

end
