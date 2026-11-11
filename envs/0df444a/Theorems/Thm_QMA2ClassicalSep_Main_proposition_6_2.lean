-- Prove2me | Theorems.Thm_QMA2ClassicalSep_Main_proposition_6_2
-- name    : QMA2ClassicalSep.Main.proposition_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:05:44.479365+00:00
-- url     : https://prove2.me/theorems/f8c8b7c5-04fe-459d-bd0d-171df67cbc47
-- title:
--   Proposition 6.2 — properties of compressed records (encoding, record growth, comparison of $C$ and $O$)
-- statement:
--   Let $k\ge2$, $s_+=N^6$, $s_-=(1-\varepsilon_0)^2\mu^2$, and let $\mathcal E$ be the query register together with any reference register $\mathbb C^d$. There are absolute constants $C_0,C_{\mathrm{rec}}>0$ such that for $\tau\in\{+,-\}$, every $R\ge0$ and $e_R(s)=C_{\mathrm{rec}}(R+1)/\sqrt s$:
--
--   1. **Encoding.** $J_\tau$ is an isometry, and $J_+|\mathcal D_+\rangle=|\emptyset\rangle$.
--   2. **Record growth.** For $\xi\in\mathrm{Rec}_{\tau,\le R}\otimes\mathcal E$, $C\xi\in\mathrm{Rec}_{\tau,\le R+6}\otimes\mathcal E$; for $\phi\in\mathcal H_\tau\otimes\mathcal E$, $J\phi\in\mathrm{Rec}_{\tau,\le R}\otimes\mathcal E\Rightarrow JO\phi\in\mathrm{Rec}_{\tau,\le R+6}\otimes\mathcal E$.
--   3. **Comparison of $C$ and $O$.** If $s_\tau\ge C_0(R+13)^2$, then for every $\phi$ with $J\phi\in\mathrm{Rec}_{\tau,\le R}\otimes\mathcal E$ and every $\xi\in\mathrm{Rec}_{\tau,\le R}\otimes\mathcal E$,
--   $$
--   \|(CJ-JO)\phi\|\le e_R(s_\tau)\|\phi\|,\qquad \|(J^\dagger C-OJ^\dagger)\xi\|\le e_{R+6}(s_\tau)\|\xi\| ,
--   $$
--   where in the NO case $P_{\mathrm{size}}\phi=\phi$ and $P_{\mathrm{size}}\xi=\xi$.
--
--   The compressed query $C$ thus tracks the true query $O$ up to a small error on small records.
--
--   Differences from the source:
--   - reading: τ ∈ {0, 1} and the constant s in (8)–(9) → τ ∈ {+, −}, with s = s_τ; reason: presentation slip: J_τ, Rec_τ and s_τ are only defined for τ ∈ {+, −}
--   - encoding: ℰ, the joint space of the query registers and any reference registers → the query register ⊗ ℂ^d for arbitrary d; operators act as identity on the factors they do not touch; reason: every such ℰ is of this form up to a unitary relabeling
--   - encoding: for every τ and R (absolute constants) → ∃ C₀, C_rec > 0 before ∀ k ≥ 2, R, d; reason: absolute constants are uniform in all parameters; k ≥ 2 is the standing assumption of §5–6
-- source:
--   Sabee Grewal, Saachi Mutreja, Kabir Tomer, A classical oracle separation between QMA and QMA(2), STOC 2027 submission #618 (October 2026), SHA-256 79883d9d08b98b41b1bb600a6644f3f578ecb803702383a9f2a58d5bc7dacedf, p. 27, Proposition 6.2 (proof pp. 27–28 and Appendix A, pp. 53–55)

import Definitions.Def_QMA2ClassicalSep_Main_Compression
open Matrix

namespace QMA2ClassicalSep.Main

theorem proposition_6_2 :
    ∃ C0 Crec : ℝ, 0 < C0 ∧ 0 < Crec ∧ ∀ k : ℕ, 2 ≤ k → ∀ (R d : ℕ),
      -- (i) Encoding
      ((jY (k := k))ᴴ * jY (k := k) = 1 ∧ (jY (k := k)).mulVec purYes = emptyRec ∧
        (jN (k := k))ᴴ * jN (k := k) = 1) ∧
      -- (ii) Record growth, YES
      (∀ ξ : YRec k × (QReg k (3 * k) × Fin d) → ℂ, SizeLe YRec.size R ξ →
        SizeLe YRec.size (R + 6) ((liftQ (Fin d) (cY (k := k))).mulVec ξ)) ∧
      (∀ φ : YESParam k × (QReg k (3 * k) × Fin d) → ℂ,
        SizeLe YRec.size R ((tensorId (QReg k (3 * k) × Fin d) (jY (k := k))).mulVec φ) →
        SizeLe YRec.size (R + 6) ((tensorId (QReg k (3 * k) × Fin d) (jY (k := k))).mulVec
          ((liftQ (Fin d) (oracleY (k := k))).mulVec φ))) ∧
      -- (ii) Record growth, NO
      (∀ ξ : NRec k × (QReg k (3 * k) × Fin d) → ℂ, SizeLe NRec.size R ξ →
        SizeLe NRec.size (R + 6) ((liftQ (Fin d) (cN (k := k))).mulVec ξ)) ∧
      (∀ φ : NOSupp k × (QReg k (3 * k) × Fin d) → ℂ,
        SizeLe NRec.size R ((tensorId (QReg k (3 * k) × Fin d) (jN (k := k))).mulVec φ) →
        SizeLe NRec.size (R + 6) ((tensorId (QReg k (3 * k) × Fin d) (jN (k := k))).mulVec
          ((liftQ (Fin d) (oracleN (k := k))).mulVec φ))) ∧
      -- (iii) Comparison of C and O, YES (s₊ = N⁶)
      (C0 * ((R : ℝ) + 13) ^ 2 ≤ ((2 : ℝ) ^ k) ^ 6 →
        (∀ φ : YESParam k × (QReg k (3 * k) × Fin d) → ℂ,
          SizeLe YRec.size R ((tensorId (QReg k (3 * k) × Fin d) (jY (k := k))).mulVec φ) →
          vnorm ((liftQ (Fin d) (cY (k := k)) * tensorId (QReg k (3 * k) × Fin d) (jY (k := k)) -
              tensorId (QReg k (3 * k) × Fin d) (jY (k := k)) * liftQ (Fin d) (oracleY (k := k))).mulVec φ) ≤
            Crec * ((R : ℝ) + 1) / Real.sqrt (((2 : ℝ) ^ k) ^ 6) * vnorm φ) ∧
        (∀ ξ : YRec k × (QReg k (3 * k) × Fin d) → ℂ, SizeLe YRec.size R ξ →
          vnorm ((tensorId (QReg k (3 * k) × Fin d) (jY (k := k))ᴴ * liftQ (Fin d) (cY (k := k)) -
              liftQ (Fin d) (oracleY (k := k)) * tensorId (QReg k (3 * k) × Fin d) (jY (k := k))ᴴ).mulVec ξ) ≤
            Crec * ((R : ℝ) + 6 + 1) / Real.sqrt (((2 : ℝ) ^ k) ^ 6) * vnorm ξ)) ∧
      -- (iii) Comparison of C and O, NO (s₋ = (1 − ε₀)²μ²), on the range of P_size
      (C0 * ((R : ℝ) + 13) ^ 2 ≤ (1 - eps0) ^ 2 * mu k ^ 2 →
        (∀ φ : NOSupp k × (QReg k (3 * k) × Fin d) → ℂ,
          (tensorId (QReg k (3 * k) × Fin d) (pSizePar (k := k))).mulVec φ = φ →
          SizeLe NRec.size R ((tensorId (QReg k (3 * k) × Fin d) (jN (k := k))).mulVec φ) →
          vnorm ((liftQ (Fin d) (cN (k := k)) * tensorId (QReg k (3 * k) × Fin d) (jN (k := k)) -
              tensorId (QReg k (3 * k) × Fin d) (jN (k := k)) * liftQ (Fin d) (oracleN (k := k))).mulVec φ) ≤
            Crec * ((R : ℝ) + 1) / Real.sqrt ((1 - eps0) ^ 2 * mu k ^ 2) * vnorm φ) ∧
        (∀ ξ : NRec k × (QReg k (3 * k) × Fin d) → ℂ,
          (tensorId (QReg k (3 * k) × Fin d) (pSizeRec (k := k))).mulVec ξ = ξ →
          SizeLe NRec.size R ξ →
          vnorm ((tensorId (QReg k (3 * k) × Fin d) (jN (k := k))ᴴ * liftQ (Fin d) (cN (k := k)) -
              liftQ (Fin d) (oracleN (k := k)) * tensorId (QReg k (3 * k) × Fin d) (jN (k := k))ᴴ).mulVec ξ) ≤
            Crec * ((R : ℝ) + 6 + 1) / Real.sqrt ((1 - eps0) ^ 2 * mu k ^ 2) * vnorm ξ)) := by sorry

end QMA2ClassicalSep.Main
