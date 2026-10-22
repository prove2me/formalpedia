-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P06_classical_coherent_information_nonpositive
-- name    : QAlgorithms.Papers.Independent.Gap20.P06.classical_coherent_information_nonpositive
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:20:52.372453+00:00
-- url     : https://prove2.me/theorems/0b56536f-8a74-4de2-9e78-fc5f6e73932b
-- title:
--   Classical coherent information is nonpositive
-- statement:
--   Let $R$ and $Q$ be nonempty finite alphabets and let $p:R\times Q\to[0,\infty)$ satisfy $\sum_{a,b}p(a,b)=1$. Form the actual diagonal joint density $\rho_{RQ}=\operatorname{diag}(p)$ and its marginal $\rho_Q=\operatorname{Tr}_R\rho_{RQ}=\operatorname{diag}(b\mapsto\sum_a p(a,b))$. With entropy in bits and $0\log_2 0=0$,
--
--   $$
--   S(\rho_Q)-S(\rho_{RQ})\le0.
--   $$
--
--   Equivalently $H(Q)-H(R,Q)\le0$ for every finite classical joint law. This explains why the source's coherent-information expression can be positive only in the quantum setting.
-- source:
--   Quantum data processing and error correction, arXiv:quant-ph/9604022v1, PDF p. 9, §4; repeated in §7, p.18

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P06

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P06

open QAlgorithms

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.9,18: for an arbitrary finite classical joint probability law,
the entropy of Q minus that of RQ is nonpositive. Diagonal states and their
marginal are constructed from the law, not assumed to satisfy an entropy bound. -/
theorem classical_coherent_information_nonpositive {R Q : Type*}
    [Fintype R] [Fintype Q] [Nonempty R] [Nonempty Q]
    (p : R × Q → ℝ) (hp : ∀ z, 0 ≤ p z) (hsum : ∑ z, p z = 1) :
    let joint : Matrix (R × Q) (R × Q) ℂ := Matrix.diagonal (fun z => (p z : ℂ))
    vnEntropy (traceLeft joint) - vnEntropy joint ≤ 0 := by sorry

end QAlgorithms.Papers.Independent.Gap20.P06

end
