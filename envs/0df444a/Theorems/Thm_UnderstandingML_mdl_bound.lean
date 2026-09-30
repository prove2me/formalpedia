-- Prove2me | Theorems.Thm_UnderstandingML_mdl_bound
-- name    : UnderstandingML.mdl_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:48:50.798986+00:00
-- url     : https://prove2.me/theorems/04808dc5-f7cd-4171-96b7-37514f79ee84
-- title:
--   Theorem 7.7 (MDL bound): for a prefix-free description language, w.p. ≥ 1 − δ every h ∈ H has L_D(h) ≤ L_S(h) + √((|h| + ln(2/δ))/(2m))
-- statement:
--   **Theorem 7.7.** Let $H$ be a hypothesis class and let $d : H \to \{0,1\}^*$ be a prefix-free description language for $H$. Then, for every sample size $m$, every confidence parameter $\delta > 0$, and every probability distribution $D$, with probability greater than $1-\delta$ over the choice of $S \sim D^m$ we have that, for all $h \in H$,
--   $$L_D(h) \le L_S(h) + \sqrt{\frac{|h| + \ln(2/\delta)}{2m}},$$
--   where $|h|$ is the length of $d(h)$.
--
--   Formally: for $m \ge 1$ and a loss with values in $[0,1]$ (the setting of §7.3, where Hoeffding's inequality gives the singleton rates), the $D^m$-probability of the failure event is at most $\delta$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §7.3 p. 90, Theorem 7.7 with its proof (from Theorem 7.4, Lemma 7.6 and Hoeffding)

import Definitions.Def_UnderstandingML_Nonuniform

open MeasureTheory

namespace UnderstandingML

/-- **Theorem 7.7** (p. 90). Let `H` be a hypothesis class and let `d : H → {0,1}*` be a
prefix-free description language for `H`. Then for every sample size `m`, every confidence
parameter `δ > 0` and every probability distribution `D`, with probability greater than
`1 − δ` over the choice of `S ∼ D^m` we have, for all `h ∈ H`,
`L_D(h) ≤ L_S(h) + √((|h| + ln(2/δ))/(2m))`, where `|h|` is the length of `d(h)`.
Stated for `m ≥ 1` and a loss with values in `[0, 1]` (the case of §7.3, where Hoeffding's
inequality gives the singleton rates); the failure probability is at most `δ`. -/
theorem mdl_bound {Z : Type*} [MeasurableSpace Z] {Hyp : Type*} (loss : Hyp → Z → ℝ)
    (H : Set Hyp) (hmeas : ∀ h ∈ H, Measurable (loss h))
    (hrange : ∀ h ∈ H, ∀ z, loss h z ∈ Set.Icc (0 : ℝ) 1) (d : Hyp → List Bool)
    (hpf : PrefixFreeOn H d) (m : ℕ) (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ) (D : Measure Z)
    [IsProbabilityMeasure D] :
    iidLaw D m {S | ∃ h ∈ H,
        empRisk loss S h + Real.sqrt (((d h).length + Real.log (2 / δ)) / (2 * m)) <
          risk loss D h} ≤ ENNReal.ofReal δ := by sorry

end UnderstandingML
