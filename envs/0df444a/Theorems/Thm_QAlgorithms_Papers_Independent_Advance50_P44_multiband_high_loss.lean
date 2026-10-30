-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P44_multiband_high_loss
-- name    : QAlgorithms.Papers.Independent.Advance50.P44.multiband_high_loss
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T09:16:35.154601+00:00
-- url     : https://prove2.me/theorems/249b75c2-8448-4d4c-9de4-fbd8e9da4059
-- title:
--   Joint high-loss asymptotic of a multiband chain
-- statement:
--   Fix a nonnegative integer $N$ and positive integer bandwidths $M_i$, with $i=0,\ldots,N$. Let the transmissivities $\eta_i(t)$ approach zero jointly, each remaining in $(0,1)$ eventually. Define the expression from Eq. (122), in bits per chain use, by
--   $$G(t)=\min_{0\le i\le N}\{-M_i\log_2(1-\eta_i(t))\}.$$
--   For every such joint approach,
--   $$\frac{G(t)}{\bigl(\min_{0\le i\le N}M_i\eta_i(t)\bigr)/\ln2}\longrightarrow1.$$
--   Different links may approach zero at different rates. The finite link set and its bandwidths are fixed. In nats the leading coefficient is one; in bits it is exactly $1/\ln2$, printed approximately as $1.44$ in Eq. (123).
--
--   **Formalization Note** An arbitrary nontrivial filter represents the joint approach. Each minimum is over the same nonempty finite set of actual link labels. This node concerns the explicit scalar expression, not a replacement definition of operational capacity.
-- source:
--   End-to-end capacities of a quantum communication network, arXiv:1905.12674v1, PDF p. 20, Unnumbered high-loss multiband scaling, Eq. (123)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P44

namespace QAlgorithms.Papers.Independent.Advance50.P44

noncomputable section

open Filter

/-- PDF p.20, Eq.(123): for a fixed finite link set and fixed positive
bandwidths, the multiband expression is asymptotic to min_i(M_i eta_i)/ln 2.
An arbitrary nontrivial filter expresses every joint high-loss approach,
including unequal rates of decay of the link transmissivities. No uniformity
in a varying repeater count or varying bandwidths is asserted. -/
theorem multiband_high_loss {A : Type*} (l : Filter A) [NeBot l]
    (N : ℕ) (M : Fin (N + 1) → ℕ) (hM : ∀ i, 0 < M i)
    (eta : A → Fin (N + 1) → ℝ)
    (heta : ∀ᶠ t in l, ∀ i, 0 < eta t i ∧ eta t i < 1)
    (hlim : ∀ i, Tendsto (fun t => eta t i) l (nhds 0)) :
    Tendsto (fun t => multibandLossExpression N M (eta t) /
      (sInf (Set.range (fun i : Fin (N + 1) => (M i : ℝ) * eta t i)) /
        Real.log 2)) l (nhds 1) := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P44
