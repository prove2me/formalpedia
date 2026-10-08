-- Prove2me | Theorems.Thm_RiskUncSets_InnerApprox_permutohull_mix_eq
-- name    : RiskUncSets.InnerApprox.permutohull_mix_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T13:06:36.569821+00:00
-- url     : https://prove2.me/theorems/063e2b35-0c5f-491d-a7cc-b8d7568f8ce2
-- title:
--   Proof of Lemma 4.2, p. 1493 — the permutohull of λq + (1 − λ)e_N is Π_q(𝒜) scaled about â by the factor λ
-- statement:
--   Let $\mathcal A = \{a_1,\dots,a_N\} \subset \mathbb R^n$ with sample mean $\hat a = Ae_N$, let $q \in \mathbb R^N$ and $\lambda \in \mathbb R$, and put $\tilde q = \lambda q + (1-\lambda) e_N$. Then
--   $$\Pi_{\tilde q}(\mathcal A) = \hat a + \lambda\,\big(\Pi_q(\mathcal A) - \hat a\big) = \{\hat a + \lambda w : w \in \tilde\pi_q(\mathcal A)\}.$$
--
--   That is, mixing a generator with the uniform generator $e_N$ scales its permutohull about the sample mean by the mixing weight $\lambda$ (for $\lambda < 0$ the set is also reflected through $\hat a$). This is the geometric fact behind Lemma 4.2 and behind the reduction of Theorem 4.5 to a one-parameter search.
--
--   **Formalization Note** The statement holds for every real vector $q$ and every $\lambda \in \mathbb R$; the page states it for $q \in \hat\Delta^N_{\mathrm{sym}}$, so this is a generalization. The proof on the page writes "$\Pi_{\tilde q}(\mathcal A)$ is a scaled version of $\Pi_{\tilde q}(\mathcal A)$"; the second set is $\Pi_q(\mathcal A)$ (a misprint).
-- source:
--   Bertsimas & Brown, Constructing uncertainty sets for robust linear optimization, Oper. Res. 57(6) (2009), p. 1493, proof of Lemma 4.2

import Mathlib
import Definitions.Def_RiskUncSets_InnerApprox_Setting
noncomputable section

namespace RiskUncSets.InnerApprox

/-- Proof of Lemma 4.2: `Π_{λq + (1−λ)e_N}(𝒜)` is `Π_q(𝒜)` scaled about `â` by `λ`,
for every `q ∈ ℝᴺ` and `λ ∈ ℝ`. -/
theorem permutohull_mix_eq {N n : ℕ} (q : Fin N → ℝ) (a : Fin N → Fin n → ℝ) (lam : ℝ) :
    permutohull (mix q lam) a = (fun w => sampleMean a + lam • w) '' piTilde q a := by sorry

end RiskUncSets.InnerApprox
