-- Prove2me | Theorems.Thm_SeedRecyclingDL_Codes_lemma_C_5
-- name    : SeedRecyclingDL.Codes.lemma_C_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:56.072596+00:00
-- url     : https://prove2.me/theorems/c91c4247-be65-4d24-835c-e5d168e34528
-- title:
--   Lemma C.5 — Computing seeds and ranks
-- statement:
--   For source-valid $m,L,b,r$, let $k=\lceil m/b\rceil$. A list $\Lambda$ of $L'$ entries has set of entries exactly $\Gamma(x)$ and may repeat entries. Procedure C.1 and sorting produce the exact sorted bad evaluation seeds using $O(L'(k+m^2))$ field operations and sorting $s_1\le L'(k-1)$ raw roots. For a good $a$, evaluation and scaled-kernel enumeration produce $P_x(a)$ and the exact sorted second bad list in $O(k+L'(k+2^{b-r}))$ field operations, sorting $s_2\le L'2^{b-r}$ raw entries.
--
--   Selecting both seeds takes $O(s_1+s_2+2)$ comparisons; recovering both ranks takes $O(\log_2(s_1+2)+\log_2(s_2+2))$. With $s=s_1+s_2$, actual uniform bit programs compute the tag and recover both additional blocks in
--   $$O\bigl(m+b+(L'+1)(m^2+2^{b-r})b^2+(s+1)b\log_2(s+2)\bigr).$$
--   For the Section 4 parameters and actual competitor enumeration, both tasks cost $O_t(n^{2t+2}\log_2^2n)$ for each fixed $t\ge1$. All repetitions remain charged. This retains the field, comparison, total-bit, and specialized bounds.
--
--   Differences from the source:
--   - encoding: binary strings and one-based positions → lists of Fin 2 with length predicates and current-word zero-based positions; reason: the order-preserving representation includes empty intermediate words and every unrestricted DL script
--   - encoding: the binary polynomial-basis field of order 2^b → a published finite-field Presentation with characteristic parameter 2, degree b, and its coefficient coordinates; reason: the quotient isomorphism and reconstruction certify the same field; coordinate order is constant coefficient first, and integer value is most significant bit first
--   - encoding: asymptotic deterministic bit complexity → finite programs with actual charged RAM executions and uniform positive constants before lengths and inputs; reason: the fixed instruction semantics generates costs; a function with an assigned runtime is not accepted
--   - reading: bit operations on a RAM without a prescribed tape layout → helper routines use length and packed-value natural cells, while main and generic decoders receive raw bit streams; reason: each cell read and output is charged by bit length; raw decoder streams permit bounded inspection of arbitrarily long invalid inputs
-- source:
--   Quan D. Bui, Manabu Hagiwara, Shuche Wang, Van Khu Vu, STOC 2027 submission #1449 (October 2026), Lemma C.5, printed p. 19 (PDF p. 21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1449.pdf

import Definitions.Def_SeedRecyclingDL_Codes_FieldExecution

set_option autoImplicit false

namespace SeedRecyclingDL.Codes

theorem lemma_C_5 :
    ∃ (first second : List FieldInstruction) (makeTag readRanks : Program) (C : ℝ), 0 < C ∧
      (∀ (F : Type) [Field F] [Fintype F] (P : FieldPresentation F), P.p = 2 →
        ∀ (m L r : ℕ) (Γ : Competitors), ValidCompetitors m L Γ →
          ValidParameters m L P.k r → ∀ (x : Word) (entries : List Word), x.length = m →
          entries.toFinset = Γ x →
          let k := blockCount m P.k
          let s₁ := (rawBadFirst P m x entries).length
          (s₁ ≤ entries.length * (k - 1)) ∧
          (∀ a : F, a ∈ badFirst P m x entries ↔
            ∃ x' ∈ Γ x, (payloadPolynomial P m x).eval a = (payloadPolynomial P m x').eval a) ∧
          (badFirst P m x entries).Pairwise (fun a b => fieldIndex P a < fieldIndex P b) ∧
          FieldExecutes P first P.k [m, r, entries.length]
            (seedFieldInputs P m x entries) (badFirst P m x entries)
            (C * entries.length * (k + (m : ℝ) ^ 2)) ∧
          (∀ a : F, a ∈ goodFirst P m Γ x →
            let s₂ := (rawBadSecond P m r x a entries).length
            s₂ ≤ entries.length * 2 ^ (P.k - r) ∧
            (∀ lam : F, lam ∈ badSecond P m r x a entries ↔
              ∃ x' ∈ Γ x, project P r (lam * (payloadPolynomial P m x).eval a) =
                project P r (lam * (payloadPolynomial P m x').eval a)) ∧
            (badSecond P m r x a entries).Pairwise (fun a b => fieldIndex P a < fieldIndex P b) ∧
            FieldExecutes P second P.k [m, r, entries.length]
              (a :: seedFieldInputs P m x entries)
              ((payloadPolynomial P m x).eval a :: badSecond P m r x a entries)
              (C * (k + entries.length * (k + (2 : ℝ) ^ (P.k - r))))) ∧
          (∀ sigma tau : Word, sigma.length = P.k - 1 → tau.length = P.k - 1 →
            let T := tag P m r Γ x sigma tau
            let a := fromBits P (T.take P.k)
            let B₁ := (badFirst P m x entries).map (fieldIndex P)
            let B₂ := (badSecond P m r x a entries).map (fieldIndex P)
            let s₂ := (rawBadSecond P m r x a entries).length
            ((selectIndex B₁ (1 + value sigma)).2 + (selectIndex B₂ (1 + value tau)).2 : ℝ) ≤
              C * (s₁ + s₂ + 2 : ℕ) ∧
            ((rankIndex B₁ (value (T.take P.k))).2 +
              (rankIndex B₂ (value ((T.drop P.k).take P.k))).2 : ℝ) ≤
              C * (log₂ (s₁ + 2) + log₂ (s₂ + 2)) ∧
            Executes makeTag P.k (badListInput P m r x entries ++ packedWord sigma ++ packedWord tau)
              (some (packedWord T)) (C * seedBitBound m P.k r entries.length (s₁ + s₂)) ∧
            Executes readRanks P.k (badListInput P m r x entries ++ packedWord T)
              (some (packedWord (sigma ++ tau))) (C * seedBitBound m P.k r entries.length (s₁ + s₂)))) ∧
      (∀ t : ℕ, 1 ≤ t → ∃ (Ct : ℝ) (n₀ : ℕ), 0 < Ct ∧ ∀ n : ℕ, n₀ ≤ n →
        ∀ (F : Type) [Field F] [Fintype F] (P : FieldPresentation F),
          P.p = 2 → P.k = fieldWidth t n → ∀ m : ℕ, 1 ≤ m → m < n →
          ∀ x sigma tau : Word, x.length = m → sigma.length = P.k - 1 → tau.length = P.k - 1 →
            let entries := listCompetitors t m x
            let Γ := competitorSet t m
            let r := hashWidth t n
            let T := tag P m r Γ x sigma tau
            Executes makeTag P.k (badListInput P m r x entries ++ packedWord sigma ++ packedWord tau)
              (some (packedWord T)) (onlineBound Ct t n) ∧
            Executes readRanks P.k (badListInput P m r x entries ++ packedWord T)
              (some (packedWord (sigma ++ tau))) (onlineBound Ct t n)) := by sorry

end SeedRecyclingDL.Codes
