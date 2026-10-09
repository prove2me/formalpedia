-- Prove2me | Theorems.Thm_SWPort_Davenport_neg_logDeriv_LFunction_le_sum_zeros
-- name    : SWPort.Davenport.neg_logDeriv_LFunction_le_sum_zeros
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T19:21:18.289156+00:00
-- url     : https://prove2.me/theorems/f673f2a9-1f2f-4f34-8634-5b5caeab7562
-- title:
--   $-\operatorname{Re}\,L'/L(s,\chi)\le c\log(q(|t|+2))-\sum_{\rho}\operatorname{Re}\frac{1}{s-\rho}$ near $\operatorname{Re}s=1$ (Davenport §14) (ported to Mathlib 0df444a)
-- statement:
--   **The zero-sum bound for $-L'/L$ near the line $\operatorname{Re}s=1$** (Davenport §14, from the Hadamard product of §12). There is an absolute constant $c>0$ such that for every modulus $q\ge1$, every non-principal Dirichlet character $\chi$ modulo $q$, every $s=\sigma+it$ with $1<\sigma\le2$, and every finite multiset $Z$ of zeros of $L(\cdot,\chi)$ lying in the closed disc $|\rho-s|\le\tfrac12$, each zero repeated at most as often as its multiplicity,
--   $$\operatorname{Re}\Bigl(-\frac{L'}{L}(s,\chi)\Bigr)\;\le\;c\log\bigl(q(|t|+2)\bigr)-\sum_{\rho\in Z}\operatorname{Re}\frac{1}{s-\rho}.$$
--   Davenport proves, for primitive $\chi$, the identity $-L'/L(s,\chi)=\tfrac12\log\tfrac q\pi+\tfrac12\tfrac{\Gamma'}{\Gamma}\bigl(\tfrac{s+a}{2}\bigr)-B(\chi)-\sum_\rho\bigl(\tfrac1{s-\rho}+\tfrac1\rho\bigr)$ with $\operatorname{Re}B(\chi)=-\sum_\rho\operatorname{Re}\tfrac1\rho$, giving $-\operatorname{Re}L'/L(s,\chi)<c\log(q(|t|+2))-\sum_\rho\operatorname{Re}\tfrac1{s-\rho}$ over *all* nontrivial zeros; since every term $\operatorname{Re}\tfrac1{s-\rho}$ is positive for $\operatorname{Re}s>1$, the sum may be restricted to any sub-multiset of the zeros, in particular to those within distance $\tfrac12$ of $s$ (a local form that can also be obtained by the Borel–Carathéodory method without the Hadamard product). Imprimitive $\chi$ reduce to the inducing primitive character, whose extra Euler factors contribute $O(\log q)$ and no zeros with $\operatorname{Re}\rho>0$. Multiplicities are expressed through Mathlib's `analyticOrderAt`. This is the central analytic input of both the zero-free region and the estimates for $\psi(x,\chi)$.
--
--   **Provenance.** This statement is the prove2.me theorem `Davenport.neg_logDeriv_LFunction_le_sum_zeros` (ebc1f4a9-b04a-4356-9fa3-3e36589066f2, statement by alya), published in the Mathlib c5ea003 (Lean 4.30.0) environment, here re-published unchanged in substance under the `SWPort` namespace for the Mathlib 0df444a environment. Its proof is a port of the accepted submission 56208df7-db43-45b6-98b5-57e452568b27 by alya, carved so that each piece fits the verifier. The port serves the Siegel–Walfisz theorem used by OpenAI's *Primitive roots for every admissible integer base* (2026), published as `ArtinPrimitiveRoots.siegel_walfisz`. The text above is the original author's natural-language statement.
-- source:
--   prove2.me user alya's proof of the Siegel–Walfisz theorem, Davenport.siegel_walfisz_ap (ff9f3207-eba1-492e-9691-e50480292b68, Mathlib c5ea003), following H. Davenport, Multiplicative Number Theory; ported to Mathlib 0df444a; original statement Davenport.neg_logDeriv_LFunction_le_sum_zeros (ebc1f4a9-b04a-4356-9fa3-3e36589066f2) by alya

import Mathlib
import Batteries.Tactic.Lemma

section

namespace SWPort

open Finset MeasureTheory Set Complex Filter Topology Asymptotics

set_option linter.unusedSectionVars false

open Classical in
theorem _root_.SWPort.Davenport.neg_logDeriv_LFunction_le_sum_zeros :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
        ∀ s : ℂ, 1 < s.re → s.re ≤ 2 →
          ∀ Z : Multiset ℂ, (∀ ρ ∈ Z, ‖ρ - s‖ ≤ 1 / 2) →
            (∀ ρ : ℂ, (Z.count ρ : ℕ∞) ≤ analyticOrderAt (DirichletCharacter.LFunction χ) ρ) →
              (-(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s)).re
                ≤ c * Real.log ((q : ℝ) * (|s.im| + 2))
                    - (Z.map fun ρ => (1 / (s - ρ)).re).sum := by
  sorry

end SWPort
end
