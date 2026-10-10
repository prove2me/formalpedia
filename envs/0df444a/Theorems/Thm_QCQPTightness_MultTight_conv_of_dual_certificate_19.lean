-- Prove2me | Theorems.Thm_QCQPTightness_MultTight_conv_of_dual_certificate_19
-- name    : QCQPTightness.MultTight.conv_of_dual_certificate_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:22:19.160222+00:00
-- url     : https://prove2.me/theorems/831c47f6-b6cc-4184-8676-de41125d4864
-- title:
--   App. B, proof of Theorem 8, p. 35 — if k ≥ m + 1, every (x̂, t̂) ∈ H with (x̂, t̂, Z) satisfying (19) lies in conv(𝒟 ∩ H)
-- statement:
--   Let the QCQP have an explicit representation $A_i = I_k\otimes\mathbb A_i$ ($i\in[\![0,m]\!]$) with symmetric $\mathbb A_i\in\mathbb S^n$, $N = kn$, and suppose $k\ge m+1$. Let $H=\{(x,t):2t=\mathrm{Opt}_{\mathrm{SDP}}\}$. Then for every $(\hat x,\hat t)\in H$ and every $Z\in\mathbb S^n$ such that $(\hat x,\hat t,Z)$ satisfies (19),
--
--   $$(\hat x,\hat t)\in\operatorname{conv}(\mathcal D\cap H).$$
--
--   This is the claim the paper proves by induction on $\operatorname{rank}(Z)$; together with dual attainment it gives $\mathcal D_{\mathrm{SDP}}\cap H\subseteq\operatorname{conv}(\mathcal D\cap H)$, the hard inclusion of Theorem 8.
--
--   **Formalization Note** The page's sentence ("for any $(\hat x,\hat t,Z)$ satisfying (19), $(\hat x,\hat t)\in\operatorname{conv}(\mathcal D\cap H)$") omits $(\hat x,\hat t)\in H$, which is the standing context of the proof ("Suppose $(\hat x,\hat t)\in\mathcal D_{\mathrm{SDP}}\cap H$") and is used in its step ("by minimality of $\hat t$"). Without it the claim is false ($Z = 0$ and a large $\hat t$ give a point of $\mathcal D$ off $H$), so it is added here. Assumption 1 and $m\ge 1$ are not needed and are dropped.
-- source:
--   arXiv:1911.09195v3, App. B, proof of Theorem 8, p. 35 (rank induction)

import Mathlib
import Definitions.Def_QCQPTightness_MultTight_QCQP
import Definitions.Def_QCQPTightness_MultTight_Mult
import Definitions.Def_QCQPTightness_MultTight_Kron

namespace QCQPTightness.MultTight

open QCQP Matrix

/-- App. B, proof of Theorem 8 (arXiv:1911.09195v3, p. 35), the rank induction: if `k ≥ m + 1`,
then for every `(x̂, t̂) ∈ H` and `Z` with `(x̂, t̂, Z)` satisfying (19),
`(x̂, t̂) ∈ conv(𝒟 ∩ H)`. The hypothesis `(x̂, t̂) ∈ H` is the proof's standing context. -/
theorem conv_of_dual_certificate_19 {N m : ℕ} (P : QCQP N m)
    {k n : ℕ} (h : k * n = N) (𝔸₀ : Matrix (Fin n) (Fin n) ℝ)
    (𝔸 : Fin m → Matrix (Fin n) (Fin n) ℝ) (hrep : P.IsKronRep h 𝔸₀ 𝔸)
    (hkm : m + 1 ≤ k) :
    ∀ (x : Fin N → ℝ) (t : ℝ) (Z : Matrix (Fin n) (Fin n) ℝ),
      (x, t) ∈ P.hyperplaneH → P.IsDualCert19 h 𝔸₀ 𝔸 x t Z →
        (x, t) ∈ convexHull ℝ (P.D ∩ P.hyperplaneH) := by sorry

end QCQPTightness.MultTight
