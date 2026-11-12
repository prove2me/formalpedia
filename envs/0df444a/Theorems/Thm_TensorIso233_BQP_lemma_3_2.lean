-- Prove2me | Theorems.Thm_TensorIso233_BQP_lemma_3_2
-- name    : TensorIso233.BQP.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:28.97884+00:00
-- url     : https://prove2.me/theorems/81e32e99-2894-475d-a54a-084d1c0ad453
-- title:
--   Lemma 3.2 — removing unused directions
-- statement:
--   Let $\mu,\mu':\mathbb Z^e\times\mathbb Z^f\to\mathbb Z^g$ be bilinear maps with the same ambient dimensions. Let $K,K'$ be their unused second-input directions and $H,H'$ their saturated output spans (2.5), and suppose $\operatorname{rank}K=\operatorname{rank}K'$ and $\operatorname{rank}H=\operatorname{rank}H'$. Then
--
--   $$
--   \mu\cong\mu'\iff\bar\mu\cong\bar\mu',
--   $$
--
--   where $\bar\mu:\mathbb Z^e\times(\mathbb Z^f/K)\to H$ is the reduced map (2.6) and $\cong$ is integral isomorphism of bilinear maps ($P\mu(u,v)=\mu'(Su,Qv)$ with $\mathbb Z$-linear isomorphisms $S,Q,P$).
--
--   The lemma is used with several shapes (Lemma 6.1, §6.2, Lemma 7.3, Proposition 7.4), which is why it is stated for all dimensions.
--
--   Differences from the source:
--   - encoding: free abelian groups E, F, G of given ambient dimensions → ℤᵉ, ℤᶠ, ℤᵍ as `Fin e → ℤ` etc.; ranks as `Module.finrank ℤ`; reason: every free abelian group of finite rank is ℤⁿ; finrank is the rank of a free ℤ-module
-- source:
--   Thomas Huffstutler, Integral 2 × 3 × 3 Tensor Isomorphism is in BQP, STOC 2027 submission #319 (October 2026), Lemma 3.2, p. 14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/319.pdf

import Definitions.Def_TensorIso233_BQP_Bilinear

namespace TensorIso233.BQP

/-- Lemma 3.2 (p. 14): for two bilinear maps `ℤᵉ × ℤᶠ → ℤᵍ` with the same ranks of the unused
directions `K` and of the saturated output span `H`, integral isomorphism is equivalent to
integral isomorphism of the reduced maps (2.6). -/
theorem lemma_3_2 {e f g : ℕ} (μ μ' : (Fin e → ℤ) →ₗ[ℤ] (Fin f → ℤ) →ₗ[ℤ] (Fin g → ℤ))
    (hK : Module.finrank ℤ (unusedDirs μ) = Module.finrank ℤ (unusedDirs μ'))
    (hH : Module.finrank ℤ (satSpan μ) = Module.finrank ℤ (satSpan μ')) :
    IsoBilin μ μ' ↔ IsoBilin (reduce μ) (reduce μ') := by sorry

end TensorIso233.BQP
