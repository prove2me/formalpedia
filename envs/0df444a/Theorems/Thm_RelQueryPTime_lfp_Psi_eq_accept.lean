-- Prove2me | Theorems.Thm_RelQueryPTime_lfp_Psi_eq_accept
-- name    : RelQueryPTime.lfp_Psi_eq_accept
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:41:55.40631+00:00
-- url     : https://prove2.me/theorems/e54d9670-ed43-446b-869a-f4a9e64f37ad
-- title:
--   Proof of Theorem 1 — one LFP decides acceptance: $\alpha(x) = S_0(x_1, x_1\dots x_r, x_r\dots x_1)$
-- statement:
--   Let $\sigma$ be a scheme, $r \ge 1$, $M$ a Turing machine with input alphabet $\{0,1\}$, and $K \ge 0$. There are a first-order formula $\Psi \in \Sigma_\alpha$ (for some $\alpha$) in which the $a$-ary relation variable occurs only positively and whose free variables are its head variables, and a map $\nu$ from the head positions to the query variables, such that for every ordered database $B$ with $n$ elements and every $r$-tuple $\bar c$:
--   $$
--   B \models \mathrm{LFP}(\Psi)(\bar c_\nu) \iff M \text{ is in its accepting state after } n^K - 1 \text{ steps on } \langle B, \bar c\rangle.
--   $$
--   Thus $\alpha(\bar x) = \mathrm{LFP}(\Psi)(\bar x_\nu)$ is a query of $\Sigma_\omega$, in its positive form, with no quantifier after the fixpoint.
--
--   **Formalization Note** Acceptance is read off Cook's run directly: the machine may halt on any cell, and halting configurations are fixed by the step function. Databases of every size are covered ($n = 0$ is vacuous for $r \ge 1$).
--
--   Differences from the source:
--   - reading: Cell(x1…xr, 0, n^k−1, qf): M is in state qf on cell 0 at time n^k−1 → the state of Cook's run after n^K − 1 steps is qaccept, on whatever cell the head is; reason: Cook's machine halts on any cell; the page assumes M ends on cell 0
--   - reading: Ψ monotone → the relation variable occurs only positively in Ψ, and Ψ ∈ Σ_α with free variables among its head; reason: this is the page's Ψ; positivity implies monotonicity
--   - generalization: the machine M of the proof, accepting S in time n^k → every machine M with input alphabet {0,1} and every K; reason: the page's M and k are an instance
-- source:
--   N. Immerman, Relational Queries Computable in Polynomial Time (Extended Abstract), Proc. 14th ACM STOC, 1982, pp.147–152, doi:10.1145/800070.802187, proof of Theorem 1, p.149 (the display Ψ(S)[z,x,p,t,a], and "Let S0 = LFP(Ψ), and let α(x1…xr) = S0(x1,x1…xr,xr…x1). Then α is equivalent to Cell(x1…xr,0,n^k−1,qf) as desired.") (PDF p.3)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_RelQueryPTime_Syntax
import Definitions.Def_RelQueryPTime_Encoding
import Definitions.Def_RelQueryPTime_Classes

namespace RelQueryPTime

/-- One `LFP` decides acceptance (Immerman, *Relational Queries Computable in Polynomial Time*, STOC 1982, proof of Theorem 1, p.149: "Let `S₀ = LFP(Ψ)`, and let
`α(x₁…x_r) = S₀(x₁,x₁…x_r,x_r…x₁)`. Then α is equivalent to `Cell(x₁…x_r,0,n^k-1,q_f)` as
desired.").

For every scheme `σ`, every arity `r ≥ 1`, every Turing machine `M` with input alphabet `Bool`
(embedded by `ι`) and every `K`, there are a first-order `Ψ ∈ Σ_α` in which the relation variable
`0` of arity `a` occurs only positively, with free variables among its head variables, and a
substitution `ν` of the query variables into the head, such that on every database `B` with
`n` elements and every `r`-tuple `c`: `B ⊨ LFP(Ψ)(ν(c))` iff `M`, run on `⟨B, c⟩`, is in its
accepting state after `n^K − 1` steps. In particular `α = LFP(Ψ)(ν(x))` is a query of `Σ_ω` in its
positive form.

**Formalization Note** Acceptance is read off `TM.run` directly; Cook's machine may halt on any
cell, and a halting configuration is a fixed point of `TM.step`. Databases of every size are
covered (`n = 0` is vacuous for `r ≥ 1`). -/
theorem lfp_Psi_eq_accept (σ : Schema) (r : ℕ) (hr : 0 < r) {Γ : Type} [Fintype Γ]
    (ι : Bool ↪ Γ) (M : CookPvsNP.TM Γ) (K : ℕ) :
    ∃ (a α : ℕ) (Ψ : Formula σ) (ν : Fin a → Fin r),
      IsSigma α Ψ ∧ Ψ.fv ⊆ {i | i < a} ∧ Ψ.Polar 0 a true ∧
      ∀ (n : ℕ) (B : Database σ n) (c : Fin r → Fin n),
        ((lfpAtom Ψ ν).query r n B c ↔
          (M.run (n ^ K - 1) (M.init ((enc B c).map ι))).state = M.qaccept) := by sorry

end RelQueryPTime
