-- Prove2me | Theorems.Thm_PeresTerno_no_communication
-- name    : PeresTerno.no_communication
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-05T11:10:02.984612+00:00
-- url     : https://prove2.me/theorems/6015745a-80bf-4759-9216-1f8dfd5d1887
-- title:
--   No-communication theorem: commuting Kraus matrices give no instantaneous information transfer
-- statement:
--   Let $\rho$ be a $d\times d$ density matrix. Let Alice's intervention have outcomes $\mu$ in a finite set $M$ with Kraus matrices $\{A_{\mu m}\}_{m\in I_\mu}$, and Bob's intervention have outcomes $\nu$ in a finite set $N$ with Kraus matrices $\{B_{\nu n}\}_{n\in J_\nu}$, all complex $d\times d$ matrices, with complete POVMs
--   $$\sum_{\mu}\sum_{m} A_{\mu m}^\dagger A_{\mu m} = \mathbb 1,\qquad \sum_{\nu}\sum_{n} B_{\nu n}^\dagger B_{\nu n} = \mathbb 1 .$$
--   Assume (Eq. (9))
--   $$[A_{\mu m}, B_{\nu n}] = 0 \qquad\text{for all } \mu, m, \nu, n .$$
--   Then for every outcome $\nu$ of Bob, the probability that Bob gets $\nu$ irrespective of Alice's result (Eq. (10)) equals the probability without Alice's intervention (Eq. (11)):
--   $$\sum_{\mu\in M} \operatorname{tr}\Big(\sum_{m\in I_\mu}\sum_{n\in J_\nu} B_{\nu n} A_{\mu m}\,\rho\,A_{\mu m}^\dagger B_{\nu n}^\dagger\Big) = \operatorname{tr}\Big(\sum_{n\in J_\nu} B_{\nu n}\,\rho\,B_{\nu n}^\dagger\Big).$$
--
--   All of Alice's operators disappear from Bob's statistics, so Eq. (9) is a sufficient condition for no instantaneous information transfer.
--
--   **Formalization Note** The completeness of Bob's POVM and the density-matrix condition on $\rho$ are part of the source's setting and are kept as hypotheses; the identity itself is a statement about complex numbers.
-- source:
--   A. Peres and D. R. Terno, Quantum information and relativity theory, Rev. Mod. Phys. 76, 93-123 (2004), https://doi.org/10.1103/RevModPhys.76.93, pp. 100-101, Sec. II.E "The no-communication theorem", Eqs. (9)-(11)

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics

open Matrix
open scoped ComplexOrder

namespace PeresTerno

theorem no_communication {d α β : Type*} [Fintype d] [DecidableEq d] [Fintype α] [Fintype β]
    {ι : α → Type*} [∀ μ, Fintype (ι μ)] {κ : β → Type*} [∀ ν, Fintype (κ ν)]
    (A : ∀ μ, ι μ → Matrix d d ℂ) (B : ∀ ν, κ ν → Matrix d d ℂ)
    (hA : ∑ μ, povmElement (A μ) = 1) (hB : ∑ ν, povmElement (B ν) = 1)
    (hAB : ∀ μ m ν n, Commute (A μ m) (B ν n))
    (ρ : Matrix d d ℂ) (hρ : IsDensityMatrix ρ) (ν : β) :
    ∑ μ, trace (∑ m, ∑ n, B ν n * A μ m * ρ * (A μ m)ᴴ * (B ν n)ᴴ)
      = trace (∑ n, B ν n * ρ * (B ν n)ᴴ) := by
  sorry

end PeresTerno
