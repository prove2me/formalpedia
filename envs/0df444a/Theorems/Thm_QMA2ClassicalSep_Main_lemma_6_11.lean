-- Prove2me | Theorems.Thm_QMA2ClassicalSep_Main_lemma_6_11
-- name    : QMA2ClassicalSep.Main.lemma_6_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:50.983108+00:00
-- url     : https://prove2.me/theorems/1219f918-b5df-4bc6-8731-1e580d4b1864
-- title:
--   Lemma 6.11 — completion and decompression: $\|(\mathrm{Dec}_{-,a}W-W\mathrm{Dec}_{+,a})\xi\|\le c_{\mathrm{dec}}\sqrt{(R+1)/N}\,\|\xi\|$
-- statement:
--   There are absolute constants $C_*,c_{\mathrm{dec}}>0$ such that for every $k\ge2$ and every integer $R\ge0$ with $N\ge C_*(R+13)$, every address $a$ and every $\xi\in\mathrm{Rec}_{+,\le R+6}\otimes\mathcal E$ (any $\mathcal E=\mathbb C^d$) satisfy
--
--   $$
--   \|(\mathrm{Dec}_{-,a}W-W\mathrm{Dec}_{+,a})\xi\|\le\delta_R\|\xi\|,\qquad\delta_R=c_{\mathrm{dec}}\sqrt{\frac{R+1}{N}} .
--   $$
--
--   Completion approximately commutes with decompression, the remaining part of a query on records.
--
--   Differences from the source:
--   - reading: C* of Lemma 6.10 and the absolute constant c_dec → ∃ C*, c_dec > 0 before ∀ k ≥ 2, R, a, d, ξ; reason: absolute constants; an existential C* here is equivalent to the shared constant (monotonicity)
--   - encoding: ℰ → ℂ^d for arbitrary d, operators acting as M ⊗ I; reason: finite-dimensional registers up to relabeling
-- source:
--   Sabee Grewal, Saachi Mutreja, Kabir Tomer, A classical oracle separation between QMA and QMA(2), STOC 2027 submission #618 (October 2026), SHA-256 79883d9d08b98b41b1bb600a6644f3f578ecb803702383a9f2a58d5bc7dacedf, p. 38, Lemma 6.11 (proof pp. 38–47)

import Definitions.Def_QMA2ClassicalSep_Main_Completion

namespace QMA2ClassicalSep.Main

theorem lemma_6_11 :
    ∃ Cstar cdec : ℝ, 0 < Cstar ∧ 0 < cdec ∧ ∀ k : ℕ, 2 ≤ k → ∀ R : ℕ,
      Cstar * ((R : ℝ) + 13) ≤ (2 : ℝ) ^ k →
      ∀ (a : Addr k (3 * k)) (d : ℕ) (ξ : YRec k × Fin d → ℂ), SizeLe YRec.size (R + 6) ξ →
        vnorm ((tensorId (Fin d) (decN a * compW (k := k) - compW (k := k) * decY a)).mulVec ξ) ≤
          cdec * Real.sqrt (((R : ℝ) + 1) / (2 : ℝ) ^ k) * vnorm ξ := by sorry

end QMA2ClassicalSep.Main
