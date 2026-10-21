-- Prove2me | Theorems.Thm_SmoothBandit_Regret_lemma_14
-- name    : SmoothBandit.Regret.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:42.769151+00:00
-- url     : https://prove2.me/theorems/c646685c-1c9f-4938-ae1b-4a4731325b79
-- title:
--   Lemma 14, p. 36 — if H_{a,k} ∈ [√d δ, 2r₀], the data support of arm a is not strongly (c₀, r₀)-regular at any point of 𝒟_{a,k} ∩ 𝒳
-- statement:
--   Consider a sample path of Algorithm 1 with horizon $T$ on an instance whose support is Lebesgue-measurable and satisfies $\mathcal X \subseteq [0,1]^d$, an epoch $1 \le k \le K$ and an arm $a = \pm1$. If the bandwidth $H_{a,k} = N_{a,k}^{-1/(2\beta+d)}$ satisfies
--
--   $$H_{a,k} \in [\sqrt d\,\delta,\ 2r_0],$$
--
--   then the data support of arm $a$, $\big((\bigcup_{j=1}^k\mathcal E_{a,j}) \cup \mathcal R_k\big) \cap \mathcal X$, is not strongly $(c_0, r_0)$-regular at any $x \in \mathcal D_{a,k} \cap \mathcal X$, where $\mathcal D_{a,k}$ is the inestimable region (6) built after epoch $k$.
--
--   This is the step that turns the screening rule (6), which tests regularity only at cube centres, into a statement about every point of the screened cubes; Lemma 5 uses it to show that the inestimable cubes can safely be handed to the other arm.
--
--   **Formalization Note.** The statement is pathwise and uses no probabilistic assumption. The containment $\mathcal X \subseteq [0,1]^d$ (part of Assumption 3) is assumed because the proof needs $\|g(x) - x\| \le \sqrt d\,\delta/2$. Both arms are covered by the quantifier over $a$.
-- source:
--   Hu, Kallus & Mao, Smooth Contextual Bandits, arXiv:1909.02553v4, p. 36, Lemma 14 (proof pp. 36–37)

import Mathlib
import Definitions.Def_SmoothBandit_Regret_Algorithm

open MeasureTheory

namespace SmoothBandit.Regret

theorem lemma_14 (d : ℕ) (hd : 1 ≤ d) (P : Params) (hP : P.Standing) (T : ℕ)
    (Ω : Type) [MeasurableSpace Ω] (M : Machine d Ω) (h𝒳 : M.𝒳 ⊆ cube d)
    (h𝒳_meas : NullMeasurableSet M.𝒳 volume)
    (ω : Ω) (k : ℕ) (hk : 1 ≤ k) (hkK : k ≤ numEpochs P d T) (a : Arm)
    (hH1 : Real.sqrt d * delta P d T ≤ Hk P T M a k ω) (hH2 : Hk P T M a k ω ≤ 2 * P.r0) :
    ∀ x ∈ M.𝒳, gIdx P d T x ∈ Dk P T M a k ω →
      ¬ StronglyRegularAt P.c0 P.r0 (suppK P T M a k ω) x := by sorry

end SmoothBandit.Regret
