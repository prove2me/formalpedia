-- Prove2me | Theorems.Thm_QMA2ClassicalSep_Main_lemma_6_12
-- name    : QMA2ClassicalSep.Main.lemma_6_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:05:38.119178+00:00
-- url     : https://prove2.me/theorems/a4534e04-cdba-46cc-a88d-56f4eb38d712
-- title:
--   Lemma 6.12 — weight on graph-concentration failures
-- statement:
--   Let $k\ge2$, let $R$ be an integer with $0\le R\le N/64$, and let $\xi\in\mathrm{Rec}_{-,\le R}\otimes\mathcal E$ (any $\mathcal E=\mathbb C^d$) with $P_{\mathrm{size}}\xi=\xi$. Then
--
--   $$
--   \|P_{\mathrm{bad}}J_-^\dagger\xi\|^2\le\gamma_R\|J_-^\dagger\xi\|^2,\qquad\gamma_R=2N^6(N+1)^R\exp(-N/8192).
--   $$
--
--   After decompression, only a negligible part of a small balanced NO record lies on parameters violating the graph-concentration condition.
--
--   Differences from the source:
--   - encoding: ℰ → ℂ^d for arbitrary d, operators acting as M ⊗ I; reason: finite-dimensional registers up to relabeling
-- source:
--   Sabee Grewal, Saachi Mutreja, Kabir Tomer, A classical oracle separation between QMA and QMA(2), STOC 2027 submission #618 (October 2026), SHA-256 79883d9d08b98b41b1bb600a6644f3f578ecb803702383a9f2a58d5bc7dacedf, p. 47, Lemma 6.12 (proof p. 48)

import Definitions.Def_QMA2ClassicalSep_Main_Compression
open Matrix

namespace QMA2ClassicalSep.Main

theorem lemma_6_12 (k : ℕ) (hk : 2 ≤ k) (R : ℕ) (hR : (R : ℝ) ≤ (2 : ℝ) ^ k / 64)
    (d : ℕ) (ξ : NRec k × Fin d → ℂ) (hξ : SizeLe NRec.size R ξ)
    (hsize : (tensorId (Fin d) (pSizeRec (k := k))).mulVec ξ = ξ) :
    vnorm ((tensorId (Fin d) (pBad (k := k))).mulVec
        ((tensorId (Fin d) (jN (k := k))ᴴ).mulVec ξ)) ^ 2 ≤
      2 * ((2 : ℝ) ^ k) ^ 6 * ((2 : ℝ) ^ k + 1) ^ R * Real.exp (-((2 : ℝ) ^ k) / 8192) *
        vnorm ((tensorId (Fin d) (jN (k := k))ᴴ).mulVec ξ) ^ 2 := by sorry

end QMA2ClassicalSep.Main
