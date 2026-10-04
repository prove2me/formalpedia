-- Prove2me | Theorems.Thm_TeschlQM_KatoRellich_relativelyBounded_tfae
-- name    : TeschlQM.KatoRellich.relativelyBounded_tfae
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T22:17:07.881899+00:00
-- url     : https://prove2.me/theorems/08bce218-f613-412e-8c02-c13c8b59c66c
-- title:
--   Lemma 6.2 — characterizations of relative boundedness
-- statement:
--   Let $A$ be a closed operator and $B$ a closable operator in a complex Hilbert space $\mathfrak{H}$, and suppose $\rho(A) \ne \emptyset$. Then the following are equivalent:
--
--   1. $B$ is $A$ bounded;
--   2. $\mathfrak{D}(A) \subseteq \mathfrak{D}(B)$;
--   3. $BR_A(z)$ is bounded (defined on all of $\mathfrak{H}$ with finite norm) for one $z \in \rho(A)$;
--   4. $BR_A(z)$ is bounded for all $z \in \rho(A)$.
--
--   Moreover, if $B$ is $A$ bounded, its $A$-bound satisfies
--   $$\text{$A$-bound of } B \;\le\; \inf_{z \in \rho(A)} \|BR_A(z)\|.$$
--
--   This lemma turns relative boundedness into a statement about bounded operators, which is how the Kato–Rellich theorem is reached.
--
--   **Formalization Note.** The hypothesis $\rho(A) \ne \emptyset$ is not printed in the book; without it "for one $z \in \rho(A)$" cannot hold while (ii) can, so the book's equivalence presupposes it. Resolvents, $\rho(A)$ and the norm $\|\cdot\| \in [0,\infty]$ are the definitions `resolventSet`, `resolvent`, `compCLM`, `opNorm` of this mission.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 134, Lemma 6.2

import Mathlib
import Definitions.Def_TeschlQM_KatoRellich_IsRelativelyBounded
import Definitions.Def_TeschlQM_KatoRellich_resolvent
import Definitions.Def_TeschlQM_KatoRellich_compCLM
import Definitions.Def_TeschlQM_KatoRellich_opNorm

namespace TeschlQM.KatoRellich

open scoped ENNReal

/-- Teschl, Lemma 6.2, p. 134. Let `A` be closed and `B` closable, and let `ρ(A) ≠ ∅` (needed for
"for one `z ∈ ρ(A)`" to be satisfiable; see the moderation notes). Then are equivalent:
(i) `B` is `A` bounded; (ii) `𝔇(A) ⊆ 𝔇(B)`; (iii) `BR_A(z)` is bounded (everywhere defined, finite
norm) for one `z ∈ ρ(A)`; (iii') the same for all `z ∈ ρ(A)`. Moreover, for `A` bounded `B`, the
`A`-bound of `B` is at most `inf_{z ∈ ρ(A)} ‖BR_A(z)‖`. -/
theorem relativelyBounded_tfae {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A B : H →ₗ.[ℂ] H) (hA : A.IsClosed) (hB : B.IsClosable)
    (hρ : (resolventSet A).Nonempty) :
    [IsRelativelyBounded A B,
      A.domain ≤ B.domain,
      ∃ z ∈ resolventSet A, (compCLM B (resolvent A z)).domain = ⊤ ∧
        opNorm (compCLM B (resolvent A z)) < ⊤,
      ∀ z ∈ resolventSet A, (compCLM B (resolvent A z)).domain = ⊤ ∧
        opNorm (compCLM B (resolvent A z)) < ⊤].TFAE ∧
    (IsRelativelyBounded A B →
      relativeBound A B ≤ ⨅ z ∈ resolventSet A, opNorm (compCLM B (resolvent A z))) := by sorry

end TeschlQM.KatoRellich
