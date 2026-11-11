-- Prove2me | Theorems.Thm_QMA2ClassicalSep_Main_theorem_6_3
-- name    : QMA2ClassicalSep.Main.theorem_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:07:01.72836+00:00
-- url     : https://prove2.me/theorems/9eb6cd98-bc56-49ac-8661-dbadef02ce07
-- title:
--   Theorem 6.3 — transfer between oracle-parameter spaces, for $T=J_-^\dagger WJ_+$
-- statement:
--   For every $k\ge2$ the map $T=T_k=J_-^\dagger WJ_+:\mathcal H_+\to\mathcal H_-$ of Equation (22) is a linear contraction. Moreover, for every polynomially bounded $R=R(k)\in\mathbb N$ there are negligible functions $\eta^{\mathrm{norm}}_R,\varepsilon^{\mathrm{query}}_R,\gamma^{\mathrm{bad}}_R$ (each $\le k^{-c}$ for all large $k$, for every $c>0$) such that for all sufficiently large $k$, every finite-dimensional register $\mathcal E$ (the query register with any $\mathbb C^d$), and every $\phi\in\mathcal H_+\otimes\mathcal E$ with $J_+\phi\in\mathrm{Rec}_{+,\le R}\otimes\mathcal E$:
--
--   $$
--   (1-\eta^{\mathrm{norm}}_R)\|\phi\|^2\le\|T\phi\|^2\le\|\phi\|^2,\qquad
--   \|(O_-T-TO_+)\phi\|\le\varepsilon^{\mathrm{query}}_R\|\phi\|,\qquad
--   \|P_{\mathrm{bad}}T\phi\|^2\le\gamma^{\mathrm{bad}}_R\|T\phi\|^2 .
--   $$
--
--   $T$ carries states of the YES oracle register to states of the NO oracle register, almost preserving norms and commuting with queries up to negligible error, while putting negligible weight on bad NO parameters.
--
--   Differences from the source:
--   - generalization: there is a family of linear contractions T_k : ℋ₊ → ℋ₋ such that … → the explicit T = J₋†WJ₊ of Equation (22) is a contraction and satisfies (10)–(12); reason: an explicit witness implies the existential statement; T is chosen before R, as in the source
--   - reading: for all input lengths k (contraction) → for all k ≥ 2; reason: the hard distributions of §5–6 are defined under the standing assumption k ≥ 2
--   - encoding: every finite-dimensional register ℰ; negligible → ℰ = query register ⊗ ℂ^d for arbitrary d; negligible f: ∀ c > 0 ∃ k₀ ∀ k ≥ k₀, f(k) ≤ k^{−c} (p. 14); reason: O_± act on the query register, so ℰ contains it; the definition of negligible is the source's
-- source:
--   Sabee Grewal, Saachi Mutreja, Kabir Tomer, A classical oracle separation between QMA and QMA(2), STOC 2027 submission #618 (October 2026), SHA-256 79883d9d08b98b41b1bb600a6644f3f578ecb803702383a9f2a58d5bc7dacedf, p. 28, Theorem 6.3 (proof pp. 49–51, Equation (22))

import Definitions.Def_QMA2ClassicalSep_Main_Completion
open Matrix

namespace QMA2ClassicalSep.Main

theorem theorem_6_3 :
    (∀ k : ℕ, 2 ≤ k → ∀ φ : YESParam k → ℂ,
      vnorm ((transferT (k := k)).mulVec φ) ≤ vnorm φ) ∧
    ∀ R : ℕ → ℕ, (∃ P : Polynomial ℕ, ∀ k, R k ≤ P.eval k) →
      ∃ ηnorm εquery γbad : ℕ → ℝ,
        (∀ c : ℝ, 0 < c → ∃ k₀ : ℕ, ∀ k ≥ k₀, ηnorm k ≤ (k : ℝ) ^ (-c)) ∧
        (∀ c : ℝ, 0 < c → ∃ k₀ : ℕ, ∀ k ≥ k₀, εquery k ≤ (k : ℝ) ^ (-c)) ∧
        (∀ c : ℝ, 0 < c → ∃ k₀ : ℕ, ∀ k ≥ k₀, γbad k ≤ (k : ℝ) ^ (-c)) ∧
        ∃ k₀ : ℕ, ∀ k ≥ k₀, 2 ≤ k → ∀ (d : ℕ) (φ : YESParam k × (QReg k (3 * k) × Fin d) → ℂ),
          SizeLe YRec.size (R k) ((tensorId (QReg k (3 * k) × Fin d) (jY (k := k))).mulVec φ) →
          ((1 - ηnorm k) * vnorm φ ^ 2 ≤
              vnorm ((tensorId (QReg k (3 * k) × Fin d) (transferT (k := k))).mulVec φ) ^ 2 ∧
            vnorm ((tensorId (QReg k (3 * k) × Fin d) (transferT (k := k))).mulVec φ) ^ 2 ≤
              vnorm φ ^ 2) ∧
          vnorm ((liftQ (Fin d) (oracleN (k := k)) *
                tensorId (QReg k (3 * k) × Fin d) (transferT (k := k)) -
              tensorId (QReg k (3 * k) × Fin d) (transferT (k := k)) *
                liftQ (Fin d) (oracleY (k := k))).mulVec φ) ≤ εquery k * vnorm φ ∧
          vnorm ((tensorId (QReg k (3 * k) × Fin d) (pBad (k := k))).mulVec
              ((tensorId (QReg k (3 * k) × Fin d) (transferT (k := k))).mulVec φ)) ^ 2 ≤
            γbad k * vnorm ((tensorId (QReg k (3 * k) × Fin d) (transferT (k := k))).mulVec φ) ^ 2 := by sorry

end QMA2ClassicalSep.Main
