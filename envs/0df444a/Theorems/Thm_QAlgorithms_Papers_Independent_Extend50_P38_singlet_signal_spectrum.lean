-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P38_singlet_signal_spectrum
-- name    : QAlgorithms.Papers.Independent.Extend50.P38.singlet_signal_spectrum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:50:19.137117+00:00
-- url     : https://prove2.me/theorems/f88fa10a-aa93-43b1-9e49-448e619d3b5c
-- title:
--   Coupled-spin spectrum of the singlet signal sum
-- statement:
--   Let $N\geq1$, $\sigma_i=2^{-(N-1)}P^-_{BA_i}\otimes I_{\bar A_i}$, and $\rho=\sum_i\sigma_i$. Here $P^-=|\psi^-\rangle\langle\psi^-|$ and $|\psi^-\rangle=(|01\rangle-|10\rangle)/\sqrt2$. In the convention $|0\rangle=|\tfrac12,-\tfrac12\rangle$, couple Alice's $N$ spins sequentially to obtain the orthonormal vectors $|\Phi^{[N]}(j,m_A,\alpha)\rangle$, retaining the entire coupling path as multiplicity label $\alpha$. For each allowed total spin $J=j+\tfrac12$ or $J=j-\tfrac12$ and magnetic number $m=-J,-J+1,\ldots,J$, form
--
--   $$|\Psi_{J,m,\alpha}\rangle=\sum_{b=0}^1\langle j,m-\mu_b;\tfrac12,\mu_b\mid J,m\rangle\,|\Phi^{[N]}(j,m-\mu_b,\alpha)\rangle_A|b\rangle_B,\qquad\mu_0=-\tfrac12,\quad\mu_1=\tfrac12.$$
--
--   These are unit vectors and obey
--
--   $$\rho|\Psi_{J,m,\alpha}\rangle=\begin{cases}\dfrac{N/2-j}{2^N}|\Psi_{J,m,\alpha}\rangle,&J=j+\tfrac12,\[2pt]\dfrac{N/2+j+1}{2^N}|\Psi_{J,m,\alpha}\rangle,&J=j-\tfrac12.\end{cases}$$
--
--   Only valid spin branches and magnetic indices occur. This gives the signal-sum eigenvectors and eigenvalues used in the SRM analysis. The full family indexed by all allowed paths, branches, and magnetic numbers is orthonormal and spans the complete Alice–Bob register. The signal sum also obeys the source recursion: appending the last Alice qubit gives the previous signal sum tensored with its identity divided by 2, plus the last-port singlet signal, with tensor factors reordered to keep Bob last.
-- source:
--   Asymptotic teleportation scheme as a universal programmable quantum processor, arXiv:0807.4568v2, PDF p. 3, Eq. (3); Appendix A pp.5–6

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P38

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P38

attribute [local instance] Classical.propDecidable Classical.decEq

-- Pinned accepted definitions; neither is re-declared in this module.

open QAlgorithms.Papers.Independent.Frontier18.P14 (singlet)

open QAlgorithms.Papers.Independent.Renew46.P01 (SpinPath)

/-- PDF p.3 Eq.(3), the complete coupled-spin basis, and the signal-sum recursion;
proved in Appendix A, PDF pp.5–6. Paths retain alpha and include the zero eigenvalue.
The recursion appends Alice's last qubit, with Bob still the final coordinate. -/
theorem singlet_signal_spectrum (N : ℕ) (hN : 0 < N) :
    (∀ p : SpinPath N, ∀ q : ℕ,
      (q = finalSpin p + 1 ∨ finalSpin p = q + 1) →
      ∀ m : ℤ, ValidMagnetic q m →
        IsState (coupledVector p q m) ∧
        act (∑ i, singletSignals N i) (coupledVector p q m) =
          ((if q = finalSpin p + 1 then lambdaMinus N ((finalSpin p : ℝ) / 2)
            else lambdaPlus N ((finalSpin p : ℝ) / 2) : ℝ) : ℂ) • coupledVector p q m) ∧
    (let V := fun l : CoupledSpinLabel N => coupledVector l.val.1 l.val.2.1 l.val.2.2
     Orthonormal ℂ V ∧ Submodule.span ℂ (Set.range V) = ⊤) ∧
    (∀ x y : AC 2 (N + 1),
      (∑ i, singletSignals (N + 1) i) x y =
        (if x.1 (Fin.last N) = y.1 (Fin.last N) then
          (∑ i, singletSignals N i)
            ((fun k : Fin N => x.1 k.castSucc), x.2)
            ((fun k : Fin N => y.1 k.castSucc), y.2) / (2 : ℂ)
        else 0) + singletSignals (N + 1) (Fin.last N) x y) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P38

end
