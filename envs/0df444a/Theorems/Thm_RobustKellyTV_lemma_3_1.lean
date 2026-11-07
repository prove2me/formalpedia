-- Prove2me | Theorems.Thm_RobustKellyTV_lemma_3_1
-- name    : RobustKellyTV.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:33:59.021127+00:00
-- url     : https://prove2.me/theorems/52887c59-9cfa-4549-a7d7-c04d664d69e8
-- title:
--   Lemma 3.1 — uniform information comparison $2\Delta(S)^2\le\Gamma(S)\le c_0^{-2}\Delta(S)^2$
-- statement:
--   Assume the standing assumptions. Let $\eta_0=\min_{A\subseteq\mathcal X:P(A)>\epsilon_0}\{P(A)-\epsilon_0\}$ and $c_0=\min\{\epsilon_0,\eta_0\}$. Then $c_0>0$, and for every $S\in\Delta_d\setminus\mathcal P_0$ (zero coordinates allowed)
--
--   $$2\Delta(S)^2\le\Gamma(S)\le c_0^{-2}\Delta(S)^2,\qquad\Delta(S)=D_{\mathrm{TV}}(S,P)-\epsilon_0 .$$
--
--   It lets the small-gap bound in terms of $\Delta(S)$ be restated in terms of $\Gamma(S)$.
--
--   Differences from the source:
--   - encoding: events A ⊆ X → finsets of Fin d; reason: the alphabet is finite
-- source:
--   A. Saha, A. Ramdas, Beyond least-favorable distribution pairs: asymptotically instance-optimal robust hypothesis testing, arXiv:2611.02130v1, §3.1, Lemma 3.1, eq. (24), p.11 (proof p.29)

import Mathlib
import Definitions.Def_RobustKellyTV_kl

namespace RobustKellyTV

/-- **Lemma 3.1** (Uniform information comparison). A. Saha, A. Ramdas, *Beyond least-favorable distribution pairs: asymptotically instance-optimal
robust hypothesis testing*, arXiv:2611.02130v1, Lemma 3.1, eq. (24), p.11.

Define `η0 = min_{A ⊆ X : P(A) > ϵ0} {P(A) − ϵ0}` and `c0 = min{ϵ0, η0} > 0`. For every
`S ∈ ∆_d \ P0`, `2∆(S)² ≤ Γ(S) ≤ c0^{−2} ∆(S)²`.

**Formalization Note.** Standing assumptions (p.6): `d ≥ 2`, `Pᵢ > 0`, `0 < ϵ0 < 1 − minᵢ Pᵢ`, bundled in `σ : Setting d`. `c0 > 0` is the first conjunct. `S` may have zero coordinates. -/
theorem lemma_3_1 {d : ℕ} (σ : Setting d) :
    0 < c0 σ ∧ ∀ S ∈ stdSimplex ℝ (Fin d), S ∉ nullBall σ →
      2 * gap σ S ^ 2 ≤ Gamma σ S ∧ Gamma σ S ≤ (c0 σ)⁻¹ ^ 2 * gap σ S ^ 2 := by sorry

end RobustKellyTV
