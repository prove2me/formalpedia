-- Prove2me | Theorems.Thm_UniformSubpower_Supplied_lemma_6_1
-- name    : UniformSubpower.Supplied.lemma_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:21:25.747477+00:00
-- url     : https://prove2.me/theorems/b416f00d-9940-495f-9ba9-c19aa20ec823
-- title:
--   Lemma 6.1 — original-table relative transport: m₀(x, y, z) for x µ y ρ z is term-independent and polynomial-time computable
-- statement:
--   Let $S$ be a finite algebra that has a Mal'tsev term of the original signature, and let $\mu \le \rho$ be congruences of $S$ with $[\rho, \mu] = 0$, i.e. the term condition $C(\rho, \mu; 0)$. Then:
--
--   1. for $x\ \mu\ y\ \rho\ z$, the value $m_0(x, y, z)$ is the same for every original Mal'tsev term $m_0$ of $S$:
--   $$m_0(x, y, z) = m_0'(x, y, z) \qquad (x\ \mu\ y\ \rho\ z,\ m_0, m_0' \text{ Mal'tsev terms});$$
--   2. all such values are computable in deterministic polynomial time from the full tables: one polynomial-time machine, on the encoding of the signature, the full tables of $S$, the tables of $\mu$ and $\rho$, and a triple $x\ \mu\ y\ \rho\ z$, outputs the binary code of $m_0(x, y, z)$, for every such input.
--
--   This "relative transport" $h(x, y, z) = m_0(x, y, z)$ is the only Mal'tsev information the paper's central charts need, and it is recovered from the original tables without knowing any Mal'tsev term.
--
--   **Formalization Note.** $[\rho, \mu] = 0$ is `TermCond ρ μ (· = ·)`; the machine is a `PvsNP.IsPolyTime` function on `encodeTransportInput`; congruences are given as Boolean tables.
--
--   Differences from the source:
--   - generalization: S one of the explicit finite factors $S_w$ → any finite algebra with an original Mal'tsev term; reason: the statement uses only finiteness, the Mal'tsev term and µ ≤ ρ, [ρ, µ] = 0, and every factor S_w is such an algebra, so the source's statement is the special case.
--   - encoding: $[\rho, \mu] = 0$ → C(ρ, µ; 0) (`TermCond`); reason: the commutator [ρ, µ] is the least δ with C(ρ, µ; δ).
--   - encoding: "all such values are computable in polynomial time from the full tables of S, µ and ρ" (word RAM) → one `PvsNP.IsPolyTime` function (Turing machine) mapping the encoded tables and a triple to the value; reason: the partial table has at most |S|³ entries, so computing all values and computing each value are polynomially equivalent, and the machine models define the same polynomial time.
-- source:
--   Gkantzounis, Uniform Subpower Membership for Finite Mal'tsev Algebras, STOC 2027 submission (manuscript sha256 149e66b1…), p. 18, Lemma 6.1

import Mathlib
import Definitions.Def_PvsNP_bitstring_encoding
import Definitions.Def_PvsNP_complexity_classes
import Definitions.Def_UniformSubpower_Supplied_Algebra
import Definitions.Def_UniformSubpower_Supplied_Encoding
import Definitions.Def_UniformSubpower_Supplied_Congruence

namespace UniformSubpower.Supplied

/-- Lemma 6.1 (Gkantzounis, p. 18): original-table relative transport. Let `S` be a finite
algebra with a Mal'tsev term of the original signature, `μ ≤ ρ` congruences of `S` with
`[ρ, μ] = 0` (the term condition `C(ρ, μ; 0)`). (1) For `x μ y ρ z`, the value `m₀(x, y, z)` is the
same for every original Mal'tsev term `m₀`. (2) One deterministic polynomial-time machine computes
it from the full tables of `S`, `μ`, `ρ` and the triple. -/
theorem lemma_6_1 :
    (∀ {σ : Signature} {S : Type} [Finite S] (alg : Alg σ S) (μ ρ : S → S → Prop),
      IsConOn alg Set.univ μ → IsConOn alg Set.univ ρ → RelLe μ ρ →
      TermCond alg ρ μ (· = ·) →
      ∀ m₀ m₀' : Term σ (Fin 3), IsMaltsevTerm alg m₀ → IsMaltsevTerm alg m₀' →
        ∀ x y z : S, μ x y → ρ y z → m₀.eval alg ![x, y, z] = m₀'.eval alg ![x, y, z]) ∧
    ∃ f : List Bool → List Bool, PvsNP.IsPolyTime f ∧
      ∀ (σ : Signature) (T : TableAlg σ) (μ ρ : Fin T.size → Fin T.size → Bool),
        IsConOn T.toAlg Set.univ (fun x y => μ x y = true) →
        IsConOn T.toAlg Set.univ (fun x y => ρ x y = true) →
        RelLe (fun x y => μ x y = true) (fun x y => ρ x y = true) →
        TermCond T.toAlg (fun x y => ρ x y = true) (fun x y => μ x y = true) (· = ·) →
        ∀ m₀ : Term σ (Fin 3), IsMaltsevTerm T.toAlg m₀ →
          ∀ x y z : Fin T.size, μ x y = true → ρ y z = true →
            f (encodeTransportInput σ T μ ρ x y z) = natCode ((m₀.eval T.toAlg ![x, y, z] : Fin T.size) : ℕ) := by sorry

end UniformSubpower.Supplied
