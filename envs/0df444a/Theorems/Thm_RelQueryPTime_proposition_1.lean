-- Prove2me | Theorems.Thm_RelQueryPTime_proposition_1
-- name    : RelQueryPTime.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:41:20.951726+00:00
-- url     : https://prove2.me/theorems/c541ac10-3985-44e4-a1a7-ad6d5980ea64
-- title:
--   Proposition 1 — $\mathrm{LFP}(\varphi)$ exists and is computable in time $p(|D|)$
-- statement:
--   Let $\varphi(S)[x_1,\dots,x_a]$ be a first-order formula of relational calculus with $\le$ whose free variables are its head variables, read as the operator $S \mapsto \{\bar u \mid B \models \varphi(S)[\bar u]\}$ on $a$-ary relations. There are a Turing machine $M$ and a polynomial $p$ such that, for every ordered database $B$ with $n$ elements on which this operator is monotone:
--
--   1. the relation $L = \mathrm{LFP}(\varphi)$ satisfies $L = \varphi(L)$ and $L \subseteq S$ for every $S$ with $\varphi(S) \subseteq S$;
--   2. on input $\langle B\rangle$, $M$ halts within $p(n)$ steps and outputs the $n^a$-bit table of $L$ (tuples in lexicographic order).
--
--   This is the easy direction of Theorem 1 for a single fixpoint: a least fixpoint of a first-order operator can be evaluated in time polynomial in the size of the domain.
--
--   **Formalization Note** The machine is Cook's one-tape Turing machine, the input is the encoding $\langle B\rangle$ with no constants, and the output is the tape from the head rightwards.
--
--   Differences from the source:
--   - generalization: φ monotone (p.148: R1 ⊆ R2 implies φ(R1) ⊆ φ(R2), for any database) → the operator need only be monotone on the database B at hand; one machine and one polynomial serve all databases; reason: a formula monotone on every database is monotone on each one, so the page's statement is the special case
--   - reading: a monotone operator φ in the language of B → φ first order (no LFP), free variables among its head variables; reason: the language of B is relational calculus (p.148), and the proof takes φ(R)[x1…xa] ≡ (Q1z1…Qkzk)M
--   - encoding: LFP(φ) exists → LFP(φ) is a fixed point contained in every relation closed under φ; reason: existence of the least fixpoint, written as a Lean statement
--   - encoding: computable in time p(|D|) → one Cook machine reads ⟨B⟩ = 1ⁿ0 and the bit tables and halts within p(n) steps with the n^a-bit table of LFP(φ) as output; reason: the page fixes no machine model, input or output format; the bound stays in the domain size n
-- source:
--   N. Immerman, Relational Queries Computable in Polynomial Time (Extended Abstract), Proc. 14th ACM STOC, 1982, pp.147–152, doi:10.1145/800070.802187, Proposition 1, p.148 (PDF p.2)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_RelQueryPTime_Syntax
import Definitions.Def_RelQueryPTime_Encoding

namespace RelQueryPTime

open Classical in
/-- Proposition 1 (Immerman, *Relational Queries Computable in Polynomial Time*, STOC 1982, p.148, due to Chandra and Harel): given a database `B` and a monotone
first-order operator `φ`, `LFP(φ)` exists and is computable in time `p(|D|)` for some polynomial `p`.

Here `φ` is a first-order formula whose free variables are its head variables `0, …, a-1`, read as
the operator `R ↦ {u | B ⊨ φ(R)[u]}` on `a`-ary relations. There are one Turing machine `M`
(Cook's model) and one polynomial `p` such that for every database `B` with `n` elements on which
this operator is monotone:
1. the relation `L = LFP(φ)` is a fixed point of the operator contained in every relation closed
   under it;
2. `M`, given the encoding `⟨B⟩`, halts within `p(n)` steps with the `n^a`-bit table of `L`
   (tuples in lexicographic order) as its output.

**Formalization Note** The input is `enc B` with no constants (`r = 0`). The polynomial bounds the
running time in the domain size `n`, as on the page, not in the input length. -/
theorem proposition_1 (σ : Schema) (a : ℕ) (φ : Formula σ) (hφ : φ.IsFO)
    (hfv : φ.fv ⊆ {i | i < a}) :
    ∃ (Γ : Type) (_ : Fintype Γ) (ι₁ : Bool ↪ Γ) (ι₂ : Bool ↪ Γ) (M : CookPvsNP.TM Γ)
      (p : Polynomial ℕ), ∀ (n : ℕ) (B : Database σ n),
        (∀ S S' : (Fin a → Fin n) → Prop, (∀ t, S t → S' t) → ∀ u : Fin a → Fin n,
          φ.eval B (envOf u) (RelEnv.set (fun _ _ _ => False) 0 a S) →
          φ.eval B (envOf u) (RelEnv.set (fun _ _ _ => False) 0 a S')) →
        ((∀ u : Fin a → Fin n, (lfpAtom φ (id : Fin a → Fin a)).query a n B u ↔
            φ.eval B (envOf u) (RelEnv.set (fun _ _ _ => False) 0 a
              (fun t => (lfpAtom φ (id : Fin a → Fin a)).query a n B t))) ∧
          (∀ S : (Fin a → Fin n) → Prop,
            (∀ u, φ.eval B (envOf u) (RelEnv.set (fun _ _ _ => False) 0 a S) → S u) →
            ∀ u, (lfpAtom φ (id : Fin a → Fin a)).query a n B u → S u) ∧
          M.HaltsWithin (p.eval n) ((enc B (Fin.elim0 : Fin 0 → Fin n)).map ι₁) ∧
          M.output (M.run (p.eval n) (M.init ((enc B (Fin.elim0 : Fin 0 → Fin n)).map ι₁))) =
            ((tuples n a).map fun t =>
              decide ((lfpAtom φ (id : Fin a → Fin a)).query a n B t)).map (some ∘ ι₂)) := by sorry

end RelQueryPTime
