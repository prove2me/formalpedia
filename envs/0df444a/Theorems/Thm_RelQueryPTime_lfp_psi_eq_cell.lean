-- Prove2me | Theorems.Thm_RelQueryPTime_lfp_psi_eq_cell
-- name    : RelQueryPTime.lfp_psi_eq_cell
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:41:11.34742+00:00
-- url     : https://prove2.me/theorems/9ffdd2e0-d9a0-40d2-919b-e1b7c7a9fcd8
-- title:
--   Proof of Theorem 1 — $\mathrm{LFP}(\psi) = \mathrm{Cell}$ for a positive first-order $\psi$
-- statement:
--   Let $\sigma$ be a scheme, $r \ge 0$, $M$ a Turing machine with input alphabet $\{0,1\}$, and $K \ge 0$; let $\ell$ be the number of possible cell contents. There is a first-order formula $\psi(S)[\bar x, \bar p, \bar t, \bar a]$, with $\bar x$ an $r$-tuple, $\bar p$ a $(K+1)$-tuple, $\bar t$ a $K$-tuple and $\bar a$ an $\ell$-tuple of head variables and no other free variables, in which $S$ occurs only positively, such that for every ordered database $B$ with $n$ elements and all tuples $\bar c, \bar p, \bar t, \bar a$:
--   $$
--   B \models \mathrm{LFP}(\psi)(\bar c, \bar p, \bar t, \bar a) \iff \bar a \text{ codes } \mathrm{Cell}_{M,\langle B,\bar c\rangle}\big(\mathrm{value}(\bar t),\ \mathrm{value}(\bar p) - n^K\big).
--   $$
--   Each application of $\psi$ adds one more row of the computation of $M$ on $\langle B,\bar c\rangle$, so the least fixpoint of $\psi$ is the whole tableau up to time $n^K - 1$.
--
--   **Formalization Note** Cell numbers are offset by $n^K$; cell contents are coded by $\ell$ bits; databases of every size are covered.
--
--   Differences from the source:
--   - reading: Cell(x,p,t,a): cell p at time t is a (p, t k-tuples, a one variable) → cell number value(p) − n^K for a (K+1)-tuple p, time value(t) for a K-tuple t, the symbol coded by an ℓ-tuple a; reason: Cook's two-way tape needs cells left of the input; the set of cell contents can be larger than the domain
--   - reading: a monotone first order expression ψ → ψ first order with the relation variable occurring only positively; reason: positivity implies monotonicity on every database (proved in the mission's sanity file), and the page's ψ is positive
--   - generalization: ψ for the machine M of the proof, accepting S in time n^k → for every machine M with input alphabet {0,1} and every K; reason: the page's M and k are an instance
-- source:
--   N. Immerman, Relational Queries Computable in Polynomial Time (Extended Abstract), Proc. 14th ACM STOC, 1982, pp.147–152, doi:10.1145/800070.802187, proof of Theorem 1, p.149 (the display ψ(S)[x,p,t,a] ≡ (t=0 ∧ M0(x,p,a)) ∨ ∃a−1a0a1(…), and "so LFP(ψ) = Cell") (PDF p.3)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_RelQueryPTime_Syntax
import Definitions.Def_RelQueryPTime_Encoding
import Definitions.Def_RelQueryPTime_TupleValue
import Definitions.Def_RelQueryPTime_Machine

namespace RelQueryPTime

/-- `LFP(ψ) = Cell` (Immerman, *Relational Queries Computable in Polynomial Time*, STOC 1982, proof of Theorem 1, p.149): there is a monotone (indeed positive) first
order `ψ(S)[x,p,t,a]` such that "each application of ψ gives us one more row of M's computation, so
LFP(ψ) = Cell".

For every scheme `σ`, arity `r`, Turing machine `M` with input alphabet `Bool` (embedded by `ι`)
and `K`, there is a first-order formula `ψ` in which the relation variable `0` (of arity
`A = r + (K+1) + K + ℓ`, `ℓ = symWidth M`) occurs only positively, with free variables among its
head variables, such that on every database `B` with `n` elements, for all tuples `c`, `p`,
`t`, `a`: `LFP(ψ)(c, p, t, a)` holds iff `a` codes the contents of cell number `value(p) − n^K` at
time `value(t)` in the run of `M` on `⟨B, c⟩`.

**Formalization Note** Head variables: `x` = `0, …, r-1`, then `p` (`K+1` variables), `t` (`K`
variables), `a` (`ℓ` variables). Times range over `0, …, n^K − 1`. Databases of every size
are covered, `n = 1` included. -/
theorem lfp_psi_eq_cell (σ : Schema) (r : ℕ) {Γ : Type} [Fintype Γ] (ι : Bool ↪ Γ)
    (M : CookPvsNP.TM Γ) (K : ℕ) :
    ∃ ψ : Formula σ, ψ.IsFO ∧ ψ.fv ⊆ {i | i < r + (K + 1) + K + symWidth M} ∧
      ψ.Polar 0 (r + (K + 1) + K + symWidth M) true ∧
      ∀ (n : ℕ) (B : Database σ n) (c : Fin r → Fin n) (p : Fin (K + 1) → Fin n)
        (t : Fin K → Fin n) (a : Fin (symWidth M) → Fin n),
        ((lfpAtom ψ (id : Fin (r + (K + 1) + K + symWidth M) → _)).query
            (r + (K + 1) + K + symWidth M) n B (Fin.append (Fin.append (Fin.append c p) t) a) ↔
          decodeSym M a = some (cell M ((enc B c).map ι) (tupleValue K t)
            ((tupleValue (K + 1) p : ℤ) - (n : ℤ) ^ K))) := by sorry

end RelQueryPTime
