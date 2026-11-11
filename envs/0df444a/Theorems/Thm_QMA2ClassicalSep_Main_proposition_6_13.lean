-- Prove2me | Theorems.Thm_QMA2ClassicalSep_Main_proposition_6_13
-- name    : QMA2ClassicalSep.Main.proposition_6_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:05:52.053911+00:00
-- url     : https://prove2.me/theorems/0060cf95-feab-4ec4-94ee-d5b2c0bc5796
-- title:
--   Proposition 6.13 — well-formedness and decoding
-- statement:
--   Let $k\ge2$. For $\tau\in\{+,-\}$ let $\Pi_\tau=J_\tau J_\tau^\dagger$ and $Q_{\tau,a}=(I-P_{\tau,a})\mathrm{Dec}_{\tau,a}P_{\tau,a}$. Then for every address $a$,
--
--   $$
--   Q_{\tau,a}\Pi_\tau=0 ,
--   $$
--
--   and for every $\xi\in\mathrm{Rec}_\tau\otimes\mathcal E$, $\|\xi\|^2-\|J_\tau^\dagger\xi\|^2=\|(I-\Pi_\tau)\xi\|^2$. In the NO case, if $s_-=(1-\varepsilon_0)^2\mu^2$ and $3R\le s_-$, every $\xi\in\mathrm{Rec}_{-,\le R}\otimes\mathcal E$ with $P_{\mathrm{size}}\xi=\xi$ satisfies
--
--   $$
--   \|(I-\Pi_-)\xi\|^2\le2\sum_a\|Q_{-,a}\xi\|^2 .
--   $$
--
--   Well-formed records are exactly those that decompression cannot shorten, and the distance from well-formedness is controlled by the operators $Q_{-,a}$.
--
--   Differences from the source:
--   - encoding: ℰ and Q_{τ,a}Π_τ = 0 as an operator identity → ℂ^d for arbitrary d; the identity Q_{τ,a}Π_τ = 0 on Rec_τ (it extends to Rec_τ ⊗ ℰ by tensoring with I); reason: finite-dimensional registers up to relabeling
-- source:
--   Sabee Grewal, Saachi Mutreja, Kabir Tomer, A classical oracle separation between QMA and QMA(2), STOC 2027 submission #618 (October 2026), SHA-256 79883d9d08b98b41b1bb600a6644f3f578ecb803702383a9f2a58d5bc7dacedf, p. 49, Proposition 6.13 (proof p. 49 and Appendix A.1, pp. 53–54)

import Definitions.Def_QMA2ClassicalSep_Main_Compression
open Matrix

namespace QMA2ClassicalSep.Main

theorem proposition_6_13 (k : ℕ) (hk : 2 ≤ k) :
    (∀ a : Addr k (3 * k), qY a * piY = 0) ∧
    (∀ a : Addr k (3 * k), qN a * piN = 0) ∧
    (∀ (d : ℕ) (ξ : YRec k × Fin d → ℂ),
      vnorm ξ ^ 2 - vnorm ((tensorId (Fin d) (jY (k := k))ᴴ).mulVec ξ) ^ 2 =
        vnorm ((tensorId (Fin d) (1 - piY (k := k))).mulVec ξ) ^ 2) ∧
    (∀ (d : ℕ) (ξ : NRec k × Fin d → ℂ),
      vnorm ξ ^ 2 - vnorm ((tensorId (Fin d) (jN (k := k))ᴴ).mulVec ξ) ^ 2 =
        vnorm ((tensorId (Fin d) (1 - piN (k := k))).mulVec ξ) ^ 2) ∧
    (∀ R : ℕ, 3 * (R : ℝ) ≤ (1 - eps0) ^ 2 * mu k ^ 2 →
      ∀ (d : ℕ) (ξ : NRec k × Fin d → ℂ), SizeLe NRec.size R ξ →
        (tensorId (Fin d) (pSizeRec (k := k))).mulVec ξ = ξ →
        vnorm ((tensorId (Fin d) (1 - piN (k := k))).mulVec ξ) ^ 2 ≤
          2 * ∑ a : Addr k (3 * k), vnorm ((tensorId (Fin d) (qN a)).mulVec ξ) ^ 2) := by sorry

end QMA2ClassicalSep.Main
