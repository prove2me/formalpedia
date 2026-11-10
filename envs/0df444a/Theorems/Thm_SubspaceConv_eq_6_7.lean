-- Prove2me | Theorems.Thm_SubspaceConv_eq_6_7
-- name    : SubspaceConv.eq_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:17:14.919042+00:00
-- url     : https://prove2.me/theorems/7f00cfce-78c7-464c-aeb9-b39a4d20f1aa
-- title:
--   Eqs. (6)–(7) — Fourier inversion on $H/B$ and the orthogonality relation
-- statement:
--   Let $B\le H=\mathbb F_q^d$, let $S$ be a commutative ring in which $q$ is invertible, and let $\psi:\mathbb F_q\to S$ satisfy $\psi(0)=1$, $\psi(a+b)=\psi(a)\psi(b)$ and $\sum_{t\in\mathbb F_q}\psi(t)=0$. Then:
--
--   1. for $\lambda\in B^\circ$, $\lambda(x+B)=\lambda^{\mathsf T}x$ is independent of the representative, so (6) and (7) are well defined;
--   2. both index sets have $q^{d-\dim B}$ entries: $|B^\circ|=|H/B|=q^{d-\dim B}$;
--   3. for every $z\in H$,
--   $$\sum_{\lambda\in B^\circ}\psi(\lambda(z))=\begin{cases}q^{d-\dim B},&z\in B,\\0,&z\notin B;\end{cases}$$
--   4. the inverse formula (7) recovers every table: for $h_B:H/B\to S$,
--   $$h_B(x+B)=q^{-(d-\dim B)}\sum_{\lambda\in B^\circ}\widehat h_\lambda(B)\,\psi(-\lambda(x)).$$
--
--   These are the local transforms the recursion applies to each coset table.
--
--   **Formalization Note** $q^{-1}$ is an element `qinv` with $q\cdot q^{-1}=1$ in $S$.
--
--   Differences from the source:
--   - generalization: values in ℂ, ψ a nontrivial additive character F_q → ℂ → any commutative ring S with q invertible, and any ψ : F → S with ψ(0) = 1, ψ(a + b) = ψ(a)ψ(b), ∑_t ψ(t) = 0; reason: a nontrivial character into ℂ satisfies these (its sum vanishes, as the paper argues), and so does ψ = ζ^Tr on the ring of §3.4, which §3.4 needs ("These identities prove Fourier orthogonality even when R has zero divisors")
--   - encoding: q^{−(d−dim B)} → qinv^(d − dim B) with q · qinv = 1; reason: the inverse of q is unique
--   - encoding: "independent of coset representatives" → λ(x + B) defined by lifting through the quotient, with the clause λ(x + B) = λᵀx; reason: same values
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §2.1, eqs. (6)–(7) and the orthogonality display, p.11 (PDF p.12)

import Mathlib
import Definitions.Def_SubspaceConv_annih
import Definitions.Def_SubspaceConv_fourier

namespace SubspaceConv

open Classical in
/-- **Eqs. (6)–(7) and the orthogonality relation**, Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §2.1, p.11 (PDF p.12). For
`B ≤ H = F_q^d`: the formulas (6)–(7) are independent of coset representatives, both index sets
`H/B` and `B°` have `q^{d − dim B}` entries, `∑_{λ ∈ B°} ψ(λ(z))` is `q^{d − dim B}` for `z ∈ B`
and `0` for `z ∉ B`, and (7) inverts (6).

**Formalization Note** Stated over any commutative ring `S` in which `q` is a unit (`qinv`) and
for any `ψ : F → S` with `ψ(0) = 1`, `ψ(a + b) = ψ(a)ψ(b)` and `∑_{t ∈ F} ψ(t) = 0`. A nontrivial
additive character into `ℂ` (the paper's §2.1) and `ψ = ζ^{Tr}` on the ring of §3.4 both satisfy
these hypotheses. Representative independence is the clause `annihEval λ (x + B) = λᵀx`. -/
theorem eq_6_7 (F : Type) [Field F] [Fintype F] [DecidableEq F] {S : Type*} [CommRing S]
    (ψ : F → S) (hψ0 : ψ 0 = 1) (hψadd : ∀ a b, ψ (a + b) = ψ a * ψ b)
    (hψsum : ∑ t : F, ψ t = 0) (qinv : S) (hq : (Fintype.card F : S) * qinv = 1)
    (d : ℕ) (B : Submodule F (Fin d → F)) :
    (∀ (lam : annih B) (x : Fin d → F),
      annihEval lam (Submodule.Quotient.mk x) = dotProduct lam.1 x) ∧
    Fintype.card (annih B) = Fintype.card F ^ (d - Module.finrank F B) ∧
    Nat.card ((Fin d → F) ⧸ B) = Fintype.card F ^ (d - Module.finrank F B) ∧
    (∀ z : Fin d → F, ∑ lam : annih B, ψ (dotProduct lam.1 z) =
      if z ∈ B then ((Fintype.card F ^ (d - Module.finrank F B) : ℕ) : S) else 0) ∧
    (∀ h : (Fin d → F) ⧸ B → S, ifourier ψ qinv (fourier ψ h) = h) := by sorry

end SubspaceConv
