-- Prove2me | Theorems.Thm_QMA2ClassicalSep_Main_lemma_6_10
-- name    : QMA2ClassicalSep.Main.lemma_6_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:35.483925+00:00
-- url     : https://prove2.me/theorems/81d97cda-c0fa-4fd8-b9d3-02bbff142ca0
-- title:
--   Lemma 6.10 — loss from the class-size restriction
-- statement:
--   Let $\rho_N=4K\exp(-\varepsilon_0^2\mu/24)$. There is an absolute constant $C_*>0$ such that for every $k\ge2$ and every integer $R\ge0$ with $N\ge C_*(R+13)$, every $\xi\in\mathrm{Rec}_{+,\le R}\otimes\mathcal E$ (any register $\mathcal E=\mathbb C^d$) satisfies
--
--   $$
--   (1-\rho_N)\|\xi\|^2\le\|W\xi\|^2\le\|\xi\|^2 .
--   $$
--
--   Restricting the completion to balanced labelings loses only a negligible part of the norm.
--
--   Differences from the source:
--   - reading: if N ≥ C*(R + 13) for some large enough constant C* → ∃ C* > 0 such that for all k ≥ 2, R, d, ξ with 2^k ≥ C*(R + 13); reason: C* is one absolute constant; stating it separately here and in Lemma 6.11 is equivalent to a shared constant, since a larger C* only strengthens the hypothesis
--   - encoding: any register ℰ → ℰ = ℂ^d for arbitrary d, W acting as W ⊗ I; reason: finite-dimensional registers up to relabeling
-- source:
--   Sabee Grewal, Saachi Mutreja, Kabir Tomer, A classical oracle separation between QMA and QMA(2), STOC 2027 submission #618 (October 2026), SHA-256 79883d9d08b98b41b1bb600a6644f3f578ecb803702383a9f2a58d5bc7dacedf, p. 37, Lemma 6.10 (proof pp. 37–38)

import Definitions.Def_QMA2ClassicalSep_Main_Completion

namespace QMA2ClassicalSep.Main

theorem lemma_6_10 :
    ∃ Cstar : ℝ, 0 < Cstar ∧ ∀ k : ℕ, 2 ≤ k → ∀ R : ℕ,
      Cstar * ((R : ℝ) + 13) ≤ (2 : ℝ) ^ k →
      ∀ (d : ℕ) (ξ : YRec k × Fin d → ℂ), SizeLe YRec.size R ξ →
        (1 - 4 * KK k * Real.exp (-(eps0 ^ 2 * mu k) / 24)) * vnorm ξ ^ 2 ≤
            vnorm ((tensorId (Fin d) (compW (k := k))).mulVec ξ) ^ 2 ∧
          vnorm ((tensorId (Fin d) (compW (k := k))).mulVec ξ) ^ 2 ≤ vnorm ξ ^ 2 := by sorry

end QMA2ClassicalSep.Main
