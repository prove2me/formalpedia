-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_renyi_channel_limit
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.renyi_channel_limit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:10:26.626155+00:00
-- url     : https://prove2.me/theorems/86749409-f9c4-46df-a78d-c0c457ec5b93
-- title:
--   Lemma 33
-- statement:
--   Let $N:A\to B$ be CPTP and $M:A\to B$ an arbitrary CP map, including zero. Channel divergences optimize over every finite reference dimension and every normalized joint input. Limits below are two-sided through positive orders other than one, in the extended real topology.
--
--   $$
--   \lim_{\alpha\to1}\widetilde D_\alpha(N\Vert M)=D(N\Vert M),\qquad\lim_{\alpha\to1}D_\alpha(N\Vert M)=D(N\Vert M).
--   $$
--
--   This is a structural property of the paper's forward communication measures.
--
--   **Formalization Note** No support or finiteness premise. The second tilde in (397) is corrected to the Petz formula (398). Sandwiched exponent corrected as documented.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 25, Lemma 33

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.Elementwise

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P09

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P06 (traceOutput)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD singleErasure)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Information100.P04 (werner)

/-- Lemma 33, arXiv:2010.01058v3, PDF pp.25,26.
No support or finiteness premise. The second tilde in (397) is corrected to the Petz formula (398). Sandwiched exponent corrected as documented.
Source correction: Printed: (149)-(150) print the sandwiched exponent -(1-alpha)/(2 alpha). Changed: Use (1-alpha)/(2 alpha). Why: At rho=sigma=I/d the printed exponent gives -2 log2 d, contradicting normalization (144) and limit (152). Printed: The purported Petz line of (397) repeats the sandwiched tilde. Changed: Use Petz divergence (398) in the second limit. Why: The statement (396), its description and the subsequent proof all identify Petz divergence. -/
theorem renyi_channel_limit {I : Type} [Fintype I] [Nonempty I]
    {J : Type} [Fintype J] [Nonempty J]
    (N M : Superop I J) (hN : IsChannel N) (hM : CP M) :
    Tendsto (fun alpha : ℝ => channelD (sandwichedD alpha) N M) orderOne
        (𝓝 (channelD relativeD N M)) ∧
      Tendsto (fun alpha : ℝ => channelD (petzD alpha) N M) orderOne
        (𝓝 (channelD relativeD N M)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
