-- Prove2me | Theorems.Thm_UniqueOptScores_lemma_2_3
-- name    : UniqueOptScores.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:27:43.084261+00:00
-- url     : https://prove2.me/theorems/38366c1e-78dc-4a84-8673-295ff317fdac
-- title:
--   Lemma 2.3 — nonemptiness needs $N \le q_0 + mq$
-- statement:
--   Fix $N$ free oracle bits $z \in \{0,1\}^N$ and all exterior answers. Suppose a deterministic transducer makes at most $q_0$ direct oracle queries and outputs a list of at most $m$ inputs $y$ for exact-one verifiers, and each verifier makes at most $q$ oracle queries on every **accepting** computation, uniformly over all assignments of the free bits and all inputs the transducer can produce. Write $c_y(z)$ for the number of accepting computations of the verifier on $y$ under assignment $z$. If the final disjunction recognizes nonemptiness, i.e. for every $z$
--   $$
--   \big(\exists\, y \text{ in the list}:\ c_y(z) = 1\big) \iff z \ne 0^N ,
--   $$
--   then
--   $$
--   N \ \le\ q_0 + m\,q .
--   $$
--   All machines are finitely clocked; there is no restriction on the number of accepting computations, and rejecting computations may make any number of queries.
--
--   This degree bound defeats every disjunctive exact-one computation on the nonemptiness witness and separates $D^A$ from $\Theta^{\mathrm P,A}_2$.
--
--   Differences from the source:
--   - encoding: finitely clocked deterministic transducer and nondeterministic exact-one verifiers on N free oracle bits → a decision tree Tr returning the list of verifier inputs, and for each input y a finite family of decision trees V y π indexed by choice sequences π; accepting count = acceptCount; reason: a finitely clocked machine on finitely many free bits is a decision tree, and a choice sequence determines one deterministic computation; same instances
--   - encoding: N free bits and all exterior answers fixed → free bit z i at the location loc i (an injection Fin N ↪ α), exterior e elsewhere (Function.extend loc z e); reason: same oracles
--   - encoding: the disjunction recognizes nonemptiness → ∀ z, (∃ y in Tr's output, acceptCount = 1) ↔ ∃ i, z i = true; reason: literal meaning
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Lemma 2.3 (restated), p.26 (stated as Lemma 2.3 in Section 2.3)

import Mathlib
import Definitions.Def_UniqueOptScores_QTree
import Definitions.Def_UniqueOptScores_acceptCount

namespace UniqueOptScores

/-- **Lemma 2.3 (nonemptiness needs many queries).**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), Lemma 2.3 (restated), p.26: "Fix N free oracle bits and all exterior answers. Suppose a
deterministic transducer, using at most q0 direct queries, produces at most m queries to exact-one
verifiers. Suppose each verifier uses at most q oracle queries on every accepting computation,
uniformly over all assignments and all inputs the transducer can produce. If the final disjunction
recognizes nonemptiness of the N free bits, then N ≤ q0 + mq. All machines are finitely clocked;
there is no restriction on the number of accepting computations."

The `N` free bits sit at the distinct locations `loc i`; under the assignment `z` the oracle is
`O_z = Function.extend loc z e` (free bit `z i` at `loc i`, exterior answer `e a` elsewhere). The
transducer is a decision tree `Tr` returning the list of verifier inputs; the verifier on input `y`
is a nondeterministic algorithm with choice sequences `π : κ y`, i.e. the family of decision trees
`V y π`, and `c_y(z) = acceptCount (V y) O_z` counts its accepting computations.

**Formalization Note.** Finitely clocked machines on finitely many free bits are decision trees.
The inner query bound covers only accepting computations, for every assignment `z'` and every `y`
that the transducer outputs under some assignment `z`. Rejecting computations are unbounded. -/
theorem lemma_2_3 {α β : Type*} {κ : β → Type*} [∀ y, Fintype (κ y)]
    (N q₀ m q : ℕ) (loc : Fin N ↪ α) (e : α → Bool)
    (Tr : QTree α (List β)) (V : (y : β) → κ y → QTree α Bool)
    (hTq : ∀ z : Fin N → Bool, (Tr.queries (Function.extend loc z e)).length ≤ q₀)
    (hTm : ∀ z : Fin N → Bool, (Tr.eval (Function.extend loc z e)).length ≤ m)
    (hVq : ∀ z z' : Fin N → Bool, ∀ y ∈ Tr.eval (Function.extend loc z e), ∀ π : κ y,
      (V y π).eval (Function.extend loc z' e) = true →
        ((V y π).queries (Function.extend loc z' e)).length ≤ q)
    (hrec : ∀ z : Fin N → Bool,
      (∃ y ∈ Tr.eval (Function.extend loc z e),
        acceptCount (V y) (Function.extend loc z e) = 1) ↔ ∃ i, z i = true) :
    N ≤ q₀ + m * q := by sorry

end UniqueOptScores
