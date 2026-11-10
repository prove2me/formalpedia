-- Prove2me | Theorems.Thm_SubspaceConv_coefficient_ring
-- name    : SubspaceConv.coefficient_ring
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:16:57.257904+00:00
-- url     : https://prove2.me/theorems/5018dd34-8d09-41a9-85b4-7597ee0febf4
-- title:
--   §3.4 — the ring $R[t]/(1+\dots+t^{p-1})$: basis $1,\dots,\zeta^{p-2}$, $\zeta^p=1$, $\sum_j\zeta^{aj}=0$, and $\psi=\zeta^{\operatorname{Tr}}$
-- statement:
--   Let $R$ be a commutative ring, $p$ a prime, and $\zeta=t\bmod(1+t+\dots+t^{p-1})$ in $R[t]/(1+t+\dots+t^{p-1})$. Then:
--
--   1. every element has a unique expansion in $1,\zeta,\dots,\zeta^{p-2}$ (these form a basis over $R$);
--   2. $R$ embeds as the constants;
--   3. $\zeta^p=1$;
--   4. $\sum_{j=0}^{p-1}\zeta^{aj}=0$ for every integer $a\not\equiv0\pmod p$;
--   5. for a finite field $\mathbb F_q$ of characteristic $p$, the function $\psi(x)=\zeta^{\operatorname{Tr}_{\mathbb F_q/\mathbb F_p}(x)}$ satisfies $\psi(0)=1$, $\psi(x+y)=\psi(x)\psi(y)$ and $\sum_{x\in\mathbb F_q}\psi(x)=0$.
--
--   Item 5 is what "these identities prove Fourier orthogonality even when $R$ has zero divisors" amounts to: these are exactly the hypotheses under which the orthogonality relation and Fourier inversion (eqs. (6)–(7)) hold. The ring supplies the character values without assuming roots of unity in $R$, and all divisions are by powers of $p$.
--
--   **Formalization Note** Items 1–4 are stated for every prime $p$. The exponent $aj$ is an integer, so $\zeta$ is used as a unit.
--
--   Differences from the source:
--   - generalization: p = char F_q → items 1–4 for every prime p; reason: the paper's p is a prime
--   - encoding: "a unique expansion in 1, t, …, t^{p−2}", "R embeds as the constants" → a basis indexed by Fin (p − 1) whose i-th vector is ζ^i; algebraMap R → R[t]/(…) injective; reason: the same statements
--   - reading: "These identities prove Fourier orthogonality even when R has zero divisors" → ψ = ζ^Tr satisfies ψ(0) = 1, ψ(x + y) = ψ(x)ψ(y) and ∑_x ψ(x) = 0 over every commutative ring R; reason: these are the hypotheses of the orthogonality and inversion milestone (eqs. (6)–(7)), which then gives orthogonality in this ring
--   - reading: "each extension operation costs O_q(1) operations in R"; "all divisions are by powers of p" → realized in the block programs of the Fourier-cost milestone and in the program model (multiplication by p⁻¹ is the only non-integer scaling), not as a separate clause; reason: these are statements about the algorithm, which the cost milestones and the goal state
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §3.4, p.13 (PDF p.14)

import Mathlib
import Definitions.Def_SubspaceConv_ExtRing
import Definitions.Def_SubspaceConv_psiTr

universe u

namespace SubspaceConv

/-- **The coefficient ring of §3.4**, Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §3.4, p.13 (PDF p.14): in
`R[t]/(1 + t + ⋯ + t^{p−1})` with `ζ = t mod (1 + ⋯ + t^{p−1})` and `ψ(x) = ζ^{Tr(x)}`, each element
has a unique expansion in `1, t, …, t^{p−2}`; `R` embeds as the constants; `ζ^p = 1` and
`∑_{j=0}^{p−1} ζ^{aj} = 0` for `a ≢ 0 (mod p)`; "these identities prove Fourier orthogonality
even when `R` has zero divisors".

**Formalization Note** Clauses 1–4 hold for every prime `p` and every commutative ring `R`
(the paper's `p = char F_q` is one case). The unique expansion is a basis indexed by
`Fin (p − 1)` whose `i`-th vector is `ζ^i`. The exponent `aj` is an integer, so `ζ` is taken as a
unit. Clause 5 states that `ψ = ζ^{Tr}` (`SubspaceConv.psiTr`, `p = char F`) satisfies the
hypotheses of the orthogonality milestone `SubspaceConv.eq_6_7`: `ψ(0) = 1`,
`ψ(x + y) = ψ(x)ψ(y)`, `∑_{x ∈ F} ψ(x) = 0`, over every commutative ring `R`. -/
theorem coefficient_ring :
    (∀ (p : ℕ), p.Prime → ∀ (R : Type u) [CommRing R],
      (∃ b : Module.Basis (Fin (p - 1)) R (ExtRing R p),
        ∀ i, b i = (AdjoinRoot.root _ : ExtRing R p) ^ (i : ℕ)) ∧
      Function.Injective (algebraMap R (ExtRing R p)) ∧
      (AdjoinRoot.root _ : ExtRing R p) ^ p = 1 ∧
      ∃ ζ : (ExtRing R p)ˣ, (ζ : ExtRing R p) = AdjoinRoot.root _ ∧
        ∀ a : ℤ, ¬ (p : ℤ) ∣ a →
          ∑ j ∈ Finset.range p, ((ζ ^ (a * (j : ℤ)) : (ExtRing R p)ˣ) : ExtRing R p) = 0) ∧
    (∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (R : Type u) [CommRing R],
      psiTr F R 0 = 1 ∧ (∀ x y : F, psiTr F R (x + y) = psiTr F R x * psiTr F R y) ∧
        ∑ x : F, psiTr F R x = 0) := by sorry

end SubspaceConv
