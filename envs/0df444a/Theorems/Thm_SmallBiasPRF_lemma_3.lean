-- Prove2me | Theorems.Thm_SmallBiasPRF_lemma_3
-- name    : SmallBiasPRF.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:11:27.569831+00:00
-- url     : https://prove2.me/theorems/937da067-9051-48b5-9f3c-c031335ac4bb
-- title:
--   Lemma 3 — linear perfect ERFs are transposes of good codes
-- statement:
--   Let $R:\mathbb F_2^{c_1}\to\mathbb F_2^{c_2}$ be linear and let $1\le k\le c_1$. Then $R$ is a perfect $k$-ERF if and only if the transpose map $R^{T}:\mathbb F_2^{c_2}\to\mathbb F_2^{c_1}$ generates a binary linear code of minimum distance at least $c_1-k+1$:
--
--   $$\mathrm{wt}\big(R^{T}(a)\big)\ \ge\ c_1-k+1\qquad\text{for every nonzero } a\in\mathbb F_2^{c_2}.$$
--
--   This reformulation of Chor et al. is what makes the ERF hypothesis usable: in Lemma 10 it turns every nonempty output mask into a single-bit mask on at least $m_2-k+1$ coordinates.
--
--   **Formalization Note** $R^T$ is the linear map of the transposed standard matrix of $R$; the weight is `hammingNorm`.
--
--   Differences from the source:
--   - encoding: the transpose map R^T → Matrix.toLin' (LinearMap.toMatrix' R)ᵀ; reason: the transpose of a linear map between coordinate spaces is the map of the transposed matrix; same map
--   - encoding: Pr[R(x) = y | x_{i_j} = x′_j for all j ∈ [c₁ − k]] = 2^{−c₂}, x′ ∈ F₂^{c₁−k} indexed through I = {i₁, …, i_{c₁−k}} → #{x : x agrees with x′ on I ∧ R x = y} · 2^{c₂} = #{x : x agrees with x′ on I}, x′ a full vector Fin c₁ → ZMod 2 read only on I (IsPerfectERF); reason: the conditioning event has 2^k > 0 elements, so the multiplied counting form is the conditional probability; a vector read on I carries exactly the same assignments; same instances
-- source:
--   Dinur–Ishai, Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with Exponentially Small Bias, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Lemma 3, p.12 (PDF 15)

import Mathlib
import Definitions.Def_SmallBiasPRF_IsPerfectERF

namespace SmallBiasPRF

/-- **Lemma 3** (linear codes and perfect ERFs), p.12 (PDF p.15).
Dinur–Ishai, *Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with
Exponentially Small Bias*, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Lemma 3, p.12 (PDF p.15).

Let `R : 𝔽₂^{c₁} → 𝔽₂^{c₂}` be linear and `1 ≤ k ≤ c₁`. Then `R` is a perfect `k`-ERF if and
only if the transpose map `Rᵀ : 𝔽₂^{c₂} → 𝔽₂^{c₁}` generates a binary linear code with minimum
distance at least `c₁ − k + 1`, namely `wt(Rᵀ(a)) ≥ c₁ − k + 1` for every nonzero `a ∈ 𝔽₂^{c₂}`.

**Formalization Note.** `Rᵀ` is the linear map of the transposed standard matrix of `R`
(`Matrix.toLin' (LinearMap.toMatrix' R)ᵀ`); `wt` is `hammingNorm`. Natural subtraction
`c₁ − k` is exact since `k ≤ c₁`. -/
theorem lemma_3 {c₁ c₂ : ℕ} (R : (Fin c₁ → ZMod 2) →ₗ[ZMod 2] (Fin c₂ → ZMod 2)) (k : ℕ)
    (hk1 : 1 ≤ k) (hkc : k ≤ c₁) :
    IsPerfectERF R k ↔
      ∀ a : Fin c₂ → ZMod 2, a ≠ 0 →
        c₁ - k + 1 ≤ hammingNorm (Matrix.toLin' (LinearMap.toMatrix' R).transpose a) := by sorry

end SmallBiasPRF
