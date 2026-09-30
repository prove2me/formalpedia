-- Prove2me | Theorems.Thm_UnderstandingML_erm_of_representative
-- name    : UnderstandingML.erm_of_representative
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:29:35.061442+00:00
-- url     : https://prove2.me/theorems/14bb5dbb-6c28-43ad-a200-4167cc52d4f9
-- title:
--   Lemma 4.2: on an ε/2-representative sample every ERM hypothesis has L_D(h_S) ≤ min_{h ∈ H} L_D(h) + ε
-- statement:
--   **Lemma 4.2.** Assume that a training set $S$ is $\frac{\epsilon}{2}$-representative (w.r.t. domain $Z$, hypothesis class $H$, loss function $\ell$, and distribution $D$). Then, any output of $ERM_H(S)$, namely, any $h_S \in \operatorname{argmin}_{h \in H} L_S(h)$, satisfies $L_D(h_S) \le \min_{h \in H} L_D(h) + \epsilon$.
--
--   Formally: if $S$ is $\epsilon/2$-representative and $h$ is an ERM hypothesis for $S$, then $L_D(h) \le L_D(h') + \epsilon$ for every $h' \in H$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §4.1 pp. 54-55, Lemma 4.2 with its proof

import Definitions.Def_UnderstandingML_Framework

open MeasureTheory

namespace UnderstandingML

/-- **Lemma 4.2** (p. 54). Assume that a training set `S` is `ε/2`-representative (w.r.t. domain
`Z`, hypothesis class `H`, loss function `ℓ`, and distribution `D`). Then any output of
`ERM_H(S)`, namely any `h_S ∈ argmin_{h ∈ H} L_S(h)`, satisfies
`L_D(h_S) ≤ min_{h ∈ H} L_D(h) + ε` (stated as `L_D(h_S) ≤ L_D(h) + ε` for every `h ∈ H`). -/
theorem erm_of_representative {Z : Type*} [MeasurableSpace Z] {Hyp : Type*}
    (loss : Hyp → Z → ℝ) (H : Set Hyp) (D : Measure Z) {ε : ℝ} {m : ℕ} (S : Fin m → Z)
    (hS : IsRepresentative loss H D (ε / 2) S) (h : Hyp) (hERM : IsERM loss H S h) :
    ∀ h' ∈ H, risk loss D h ≤ risk loss D h' + ε := by sorry

end UnderstandingML
