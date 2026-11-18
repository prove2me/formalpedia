-- Prove2me | Theorems.Thm_RandomDimReduction_Channel_RTP_isQuantumChannel
-- name    : RandomDimReduction.Channel.RTP_isQuantumChannel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T17:59:14.106548+00:00
-- url     : https://prove2.me/theorems/425af230-8640-44f1-b6c3-47006efe6bf5
-- title:
--   The moment-defined dimension reduction is a quantum channel
-- statement:
--   Let $n,k,d$ be positive integers with $k\le d$. Let $M$ be the Grassmannian moment in Eq. (2), let $A=\sqrt{M^+}$, and let $Q$ be the orthogonal projector onto its kernel. Define the map on every complex operator $X$ on $(\mathbb C^d)^{\otimes n}$ by
--   $$R^{\mathrm{TP}}(X)=\mathbb E_V\big[((VW_0)^{\otimes n})^\dagger A X A(VW_0)^{\otimes n}\big]+\operatorname{tr}(QX)\frac{I}{k^n}.$$
--   Then this map is complex-linear, completely positive, and trace preserving:
--   $$R^{\mathrm{TP}}:\mathcal L((\mathbb C^d)^{\otimes n})\longrightarrow\mathcal L((\mathbb C^k)^{\otimes n})\quad\text{is a quantum channel}.$$
--   The assertion concerns the entire operator space and includes the contribution from the kernel of the moment. This is the channel-validity part of Theorem 1.1 and supplies a reusable foundation for its exact identity and implementation conclusions.
-- source:
--   Angus Lowe and Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), Theorem 1.1 p.2 and Section 2.2 pp.6–7, Eq.(3) and its channel-validity discussion. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf

import Definitions.Def_RandomDimReduction_Channel_Moment

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

theorem RTP_isQuantumChannel (n k d : ℕ) (hn : 0 < n) (hk : 1 ≤ k) (hkd : k ≤ d) :
    ∃ L : Op (Word n d) →ₗ[ℂ] Op (Word n k),
      (∀ X, L X = RTP n k d X) ∧ WildeQIT.EntBreaking.IsQuantumChannel L := by sorry

end RandomDimReduction.Channel
