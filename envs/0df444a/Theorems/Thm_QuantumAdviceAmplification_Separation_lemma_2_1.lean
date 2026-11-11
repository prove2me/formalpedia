-- Prove2me | Theorems.Thm_QuantumAdviceAmplification_Separation_lemma_2_1
-- name    : QuantumAdviceAmplification.Separation.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:05:03.718856+00:00
-- url     : https://prove2.me/theorems/b5aa045d-679b-46ce-89ba-7b7a72f8c18d
-- title:
--   Lemma 2.1 — Entropy perturbation
-- statement:
--   Let $0\le\varepsilon_1\le\varepsilon_0\le1/2$. With binary entropy $H$ in bits and the envelope $\Phi$ defined in Section 2.1,
--   $$\varepsilon_0-\varepsilon_1\le\Phi(\varepsilon_1,H(\varepsilon_0)-H(\varepsilon_1)).$$
--   Equivalently, $H(\varepsilon_0)\le H(\varepsilon_1)+\theta$ implies $\varepsilon_0\le\varepsilon_1+\Phi(\varepsilon_1,\theta)$.
--
--   This controls the change in error produced by an entropy-budget perturbation.
--
--   Differences from the source: none.
-- source:
--   Shih-Han Hung, Han-Hsuan Lin, STOC 2027 submission #1297 (October 2026), p.4, Lemma 2.1

import Definitions.Def_QuantumAdviceAmplification_Separation_parameters
set_option autoImplicit false
open Classical

namespace QuantumAdviceAmplification.Separation

theorem lemma_2_1 (ε1 ε0 : ℝ) (h1 : 0 ≤ ε1) (h10 : ε1 ≤ ε0) (h0 : ε0 ≤ 1 / 2) :
    ε0 - ε1 ≤ Φ ε1 (H ε0 - H ε1) ∧
    ∀ θ : ℝ, H ε0 ≤ H ε1 + θ → ε0 ≤ ε1 + Φ ε1 θ := by sorry

end QuantumAdviceAmplification.Separation
