-- Prove2me | Theorems.Thm_SubspaceConv_fourier_cost
-- name    : SubspaceConv.fourier_cost
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:17:13.992185+00:00
-- url     : https://prove2.me/theorems/764fde5d-7419-407a-97ed-1f8fc6e48f2c
-- title:
--   §2.1 — the Fourier transforms (6)–(7) in $O_q((d+1)|H/B|)$ operations over the ring of §3.4
-- statement:
--   There is a constant $c$, depending only on $\mathbb F_q$, with the following property. For every $d$ and every $B\le H=\mathbb F_q^d$ there are two well-formed linear straight-line programs $\Phi,\Phi'$, each with at most
--   $$c\,(d+1)\,|H/B|$$
--   operations, such that for every commutative ring $A$ in which $p=\operatorname{char}\mathbb F_q$ is invertible:
--
--   1. $\Phi$ computes the Fourier transform (6) of tables $H/B\to A[t]/(1+\dots+t^{p-1})$ with $\psi(x)=\zeta^{\operatorname{Tr}(x)}$;
--   2. $\Phi'$ computes the inverse formula (7) for tables $B^\circ\to A[t]/(1+\dots+t^{p-1})$, with $q^{-1}$ the inverse of $q$ in that ring.
--
--   Each element of $A[t]/(1+\dots+t^{p-1})$ is carried by a block of $p-1$ registers holding its coordinates in $1,\zeta,\dots,\zeta^{p-2}$; a table is one block per coset, resp. per frequency. The paper obtains the count by identifying $H/B$ with $\mathbb F_p^{m(d-\dim B)}$ and applying a length-$p$ transform along each coordinate, and §3.4 implements these formulas over the stated coefficient rings. Summed over the directions of one recursive call, this is the $O_q(nM_q(n,k))$ local Fourier work of §3.3.
--
--   **Formalization Note** A program is one fixed list of gates, valid over every such ring $A$; $c$ is chosen before $d$ and $B$.
--
--   Differences from the source:
--   - reading: "taking O_q((d+1)|H/B|) operations. Section 3.4 implements these formulas over the stated coefficient rings" → linear straight-line programs over A acting on blocks of p − 1 registers that encode elements of A[t]/(1 + ⋯ + t^{p−1}), computing (6) and (7) with ψ = ζ^Tr, cost ≤ c(d + 1)|H/B|; reason: this is how the recursion uses the count over a general coefficient ring (§3.4); over ℂ alone the sentence fixes no cost model
--   - generalization: for each ring, O_q((d+1)|H/B|) ring operations → one program per (d, B), valid over every commutative ring A with p · pinv = 1, with only additions, subtractions, integer scalings and multiplications by p⁻¹; reason: multiplication by ζ^j on blocks is integer-linear and q^{−1} is a power of p^{−1}; a ring-uniform program is in particular an algorithm for each ring
--   - encoding: q^{−(d−dim B)} in the ring of §3.4 → qinv^(d − dim B) for any qinv with q · qinv = 1 in A[t]/(1 + ⋯ + t^{p−1}); reason: the inverse is unique
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §2.1, last two sentences, p.11 (PDF p.12), with §3.4, p.13

import Mathlib
import Definitions.Def_SubspaceConv_LinSLP
import Definitions.Def_SubspaceConv_annih
import Definitions.Def_SubspaceConv_fourier
import Definitions.Def_SubspaceConv_ExtRing
import Definitions.Def_SubspaceConv_psiTr

universe u

namespace SubspaceConv

/-- **Cost of the Fourier transforms** (§2.1, last two sentences, with §3.4),
Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §2.1, p.11 (PDF p.12): identifying `H/B` with `F_p^{m(d − dim B)}` and applying a
length-`p` transform along each coordinate, (6) and (7) take `O_q((d + 1)|H/B|)` operations, and
§3.4 implements them over the stated coefficient rings.

**Formalization Note** There is `c`, depending only on `F`, such that for every `d` and
`B ≤ F^d` two well-formed linear straight-line programs `Φ`, `Φ'` with at most
`c (d + 1) |H/B|` operations compute (6) and (7) with `ψ = ζ^{Tr}` over `ExtRing A p`
(`p = char F`), for every commutative ring `A` with `p · pinv = 1`. An element of
`ExtRing A p` is carried by a block of `p − 1` registers (its coordinates in `1, ζ, …, ζ^{p−2}`,
read through `dec`); a table on `H/B` (resp. `B°`) is a block per coset (resp. frequency).
For (7), `qinv` is any inverse of `q` in `ExtRing A p`. -/
theorem fourier_cost (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    ∃ c : ℕ, ∀ (d : ℕ) (B : Submodule F (Fin d → F)),
      ∃ (Φ : LinSLP (((Fin d → F) ⧸ B) × Fin (ringChar F - 1)) (annih B × Fin (ringChar F - 1)))
        (Φ' : LinSLP (annih B × Fin (ringChar F - 1)) (((Fin d → F) ⧸ B) × Fin (ringChar F - 1))),
        Φ.WellFormed ∧ Φ'.WellFormed ∧
        Φ.cost ≤ c * (d + 1) * Nat.card ((Fin d → F) ⧸ B) ∧
        Φ'.cost ≤ c * (d + 1) * Nat.card ((Fin d → F) ⧸ B) ∧
        ∀ (A : Type u) [CommRing A] (pinv : A), (ringChar F : A) * pinv = 1 →
          (∀ (v : ((Fin d → F) ⧸ B) × Fin (ringChar F - 1) → A) (lam : annih B),
            dec (fun i => Φ.eval pinv v (lam, i)) =
              fourier (psiTr F A) (fun c => dec (fun i => v (c, i))) lam) ∧
          (∀ qinv : ExtRing A (ringChar F), (Fintype.card F : ExtRing A (ringChar F)) * qinv = 1 →
            ∀ (w : annih B × Fin (ringChar F - 1) → A) (c : (Fin d → F) ⧸ B),
              dec (fun i => Φ'.eval pinv w (c, i)) =
                ifourier (psiTr F A) qinv (fun lam => dec (fun i => w (lam, i))) c) := by sorry

end SubspaceConv
