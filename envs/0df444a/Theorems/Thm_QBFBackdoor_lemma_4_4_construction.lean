-- Prove2me | Theorems.Thm_QBFBackdoor_lemma_4_4_construction
-- name    : QBFBackdoor.lemma_4_4_construction
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:32:54.846438+00:00
-- url     : https://prove2.me/theorems/41232e26-57b7-4c8d-a052-5845a056e948
-- title:
--   Proof of Lemma 4.4 — the guarded construction: equivalence, a backdoor of size $\lceil\log_2 k\rceil$, output length
-- statement:
--   Let $\mathcal C$ be any class of conjunctive matrices over an arbitrary type of atoms, and let $\Phi=Q.(\phi_1\vee\cdots\vee\phi_k)$ with $k\ge1$ and $h=\lceil\log_2k\rceil$. Then there is a conjunction of guarded atoms $R\vee T$, with $R$ an atom of some $\phi_i$ and $T$ a clause on $h$ fresh variables $Z$, such that, for $\Phi'=Q\,\exists Z.\ \bigwedge(R\vee T)$:
--
--   1. $\Phi'$ is true if and only if $\Phi$ is true;
--   2. for every assignment $\tau$ to $Z$, deleting the atoms made true by $\tau$ leaves exactly one of the disjuncts $\phi_i$; in particular $Z$, of size $h$, is a strong backdoor of $\Phi'$ to QBF$(\mathcal C)$ whenever every $\phi_i$ is in $\mathcal C$;
--   3. $\lVert\Phi'\rVert\le C_0\,(1+h)\,\lVert\Phi\rVert$ for an absolute constant $C_0$.
--
--   For clausal input, the guarded atoms are the clauses $R\cup T$ and $\Phi'$ is a CNF QBF with the same properties.
--
--   This is the step that turns a constant number of disjuncts into a constant-size backdoor. With four disjuncts it produces a backdoor of size two.
--
--   Differences from the source:
--   - generalization: the proof's claims on the construction: "restriction leaves exactly ϕi after deleting true atoms. Hence Z is a strong backdoor to QBF(C)" → also: equivalence of Φ′ and Φ (next paragraph of the proof), the output length O((1 + ⌈log2 k⌉)∥Φ∥) and the CNF form for clausal input (statement of Lemma 4.4); reason: all are claims of the same lemma and proof; dropping them gives the quoted claims
--   - encoding: O((1 + ⌈log2 k⌉)∥Φ∥) output length → ∃ absolute C₀, guardedSize ≤ C₀ (1 + h) disjSize; reason: ∥·∥ counts one symbol per prefix variable, disjunct, atom, guard literal, plus the atom lengths (§3.1)
--   - encoding: the residual Φ′[τ] for τ : Z → {0,1} → the list residual τ atoms under the original prefix, equal to the i-th disjunct; reason: Z is fresh, so no atom R mentions Z and Φ′[τ] keeps R itself
--   - encoding: variables x1, …, xn and prefix Q1x1 … Qnxn → variables Fin n quantified in index order, q j = true meaning ∃; reason: relabelling; same formulas
-- source:
--   Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, Backdoors for Quantified Boolean Formulas, arXiv:2604.15927 (held version, sha256 3ea1662e…), proof of Lemma 4.4, pp.20–21; Lemma 4.4, p.20 (output length, clausal input)

import Mathlib
import Definitions.Def_QBFBackdoor_guardedSat

namespace QBFBackdoor

open MDPComplexity.PartiallyObserved

/-- **The guarded construction of the proof of Lemma 4.4 (from k disjuncts back to a backdoor of
size ⌈log₂ k⌉).** Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, *Backdoors for
Quantified Boolean Formulas*, arXiv:2604.15927 (held version, sha256 3ea1662e…), proof of
Lemma 4.4, pp.20–21: "Let Φ = Q. ⋁_{i=1}^k ϕi and h = ⌈log2 k⌉. Pad the list to p = 2^h disjuncts
by repeating its first p − k members. … Introduce Z = {z1, . . . , zh} and enumerate its assignments
as t1, . . . , tp. Let Ti be the clause on Z falsified exactly by ti. Replace each atom R of ϕi by
the guarded atom R ∨ Ti, obtaining ϕ′i, and output Φ′ = Q∃Z. ⋀_{i=1}^p ϕ′i. For h = 0 the guard is
the empty clause. For every assignment Z = ti, restriction leaves exactly ϕi after deleting true
atoms. Hence Z is a strong backdoor to QBF(C)." The equivalence is the next paragraph of the proof,
and the output length `O((1 + ⌈log2 k⌉)∥Φ∥)` is the statement of Lemma 4.4, p.20, where `C` is
"a class of conjunctive matrices and k ≥ 1"; "For clausal input, the output is explicitly CNF."

There is an absolute constant `C₀` such that, for every atom type `α` with semantics `sat` and
length `sz`, every prefix `q` on `n` variables and every list of `k ≥ 1` disjuncts, with
`h = ⌈log₂ k⌉`, there is a conjunction of guarded atoms `R ∨ T` (`R` an atom of `α`, `T` a clause
on `h` fresh existential variables `Z`) such that:
1. `Q∃Z.⋀(R ∨ T)` is true iff `Q.⋁ϕ_i` is true;
2. for every assignment `τ` to `Z`, deleting the atoms made true by `τ` leaves exactly one of the
   disjuncts `ϕ_i`, so `Z` (of size `h`) is a strong backdoor: for every class `C` of conjunctive
   matrices containing all the `ϕ_i`, every such restriction lies in `C`;
3. the output length is at most `C₀ (1 + h) ∥Φ∥`.

For clausal input (`α` the clauses on `Fin n`), the output written as a CNF QBF, with the clauses
`R ∪ T` (`guardedCNF`), is true iff `Φ` is, and has the same restrictions and length bound.

**Formalization Note** `C` is arbitrary: the atoms are of an arbitrary type. Since `Z` is fresh, no
atom `R` mentions `Z`, so restricting by `τ` leaves `R` itself; the restricted formula is the list
`residual τ atoms` under the original prefix. The lengths `∥Φ∥` and `∥Φ′∥` are `disjSize` and
`guardedSize` (§3.1). This item does not contain Lemma 4.4's running-time clause
`O((1 + ⌈log2 k⌉)∥Φ∥)` time, which is measured in the paper's unit-cost symbol model (§3.1). -/
theorem lemma_4_4_construction :
    ∃ C₀ : ℕ,
      (∀ (α : Type) (n : ℕ) (sat : α → (Fin n → Bool) → Prop) (sz : α → ℕ)
        (q : Fin n → Bool) (disj : List (List α)), 1 ≤ disj.length →
        ∃ atoms : List (α × Finset (Fin (Nat.clog 2 disj.length) × Bool)),
          (PrefixHolds (Fin.append q (fun _ => true)) (fun x => ∀ a ∈ atoms, guardedSat sat a x) ↔
            PrefixHolds q (disjSat sat disj)) ∧
          (∀ τ : Fin (Nat.clog 2 disj.length) → Bool,
            ∃ i : Fin disj.length, residual τ atoms = disj.get i) ∧
          (∀ C : List α → Prop, (∀ ϕ ∈ disj, C ϕ) →
            ∀ τ : Fin (Nat.clog 2 disj.length) → Bool, C (residual τ atoms)) ∧
          guardedSize sz n atoms ≤ C₀ * (1 + Nat.clog 2 disj.length) * disjSize sz n disj) ∧
      (∀ (n : ℕ) (q : Fin n → Bool) (disj : List (List (Finset (Fin n × Bool)))),
        1 ≤ disj.length →
        ∃ atoms : List (Finset (Fin n × Bool) × Finset (Fin (Nat.clog 2 disj.length) × Bool)),
          ((guardedCNF q atoms).holds ↔
            PrefixHolds q (disjSat (fun c x => ∃ l ∈ c, x l.1 = l.2) disj)) ∧
          (∀ τ : Fin (Nat.clog 2 disj.length) → Bool,
            ∃ i : Fin disj.length, residual τ atoms = disj.get i) ∧
          guardedSize (fun c => c.card) n atoms ≤
            C₀ * (1 + Nat.clog 2 disj.length) * disjSize (fun c => c.card) n disj) := by sorry

end QBFBackdoor
