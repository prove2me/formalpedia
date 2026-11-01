-- Prove2me | Theorems.Thm_ShorAdditivityEquiv_dual_tight_at_signal_states
-- name    : ShorAdditivityEquiv.dual_tight_at_signal_states
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:31:07.783895+00:00
-- url     : https://prove2.me/theorems/1f3fbf33-fbef-4796-a90f-82847f255e8d
-- title:
--   §5, pp. 11–12 — equality holds in (13) at the signal states of an optimal decomposition
-- statement:
--   Let $N$ be a quantum channel, $\rho$ a density matrix, and $\{p_x,|v_x\rangle\}$ an optimal decomposition of $\rho$: $\sum_x p_x|v_x\rangle\langle v_x|=\rho$ and its Holevo quantity equals $\chi_N(\rho)$. Let $f=\mathrm{Tr}\,\tau\,\cdot$ ($\tau$ Hermitian) be an optimal dual function: $f(|v\rangle\langle v|)\le H(N(|v\rangle\langle v|))$ for every unit vector $|v\rangle$ in the support of $\rho$, and $\chi_N(\rho)=H(N(\rho))-f(\rho)$. Then for every signal state, i.e. every $x$ with $p_x>0$,
--   $$
--   f(|v_x\rangle\langle v_x|) = H\big(N(|v_x\rangle\langle v_x|)\big).
--   $$
--   This is complementary slackness for the linear program of §5, used in §6 to compare the dual functions of $N_1$, $N_2$ and $N_1\otimes N_2$ at the signal states.
--
--   Differences from the source:
--   - generalization: f feasible for (13): f(|v⟩⟨v|) ≤ H(N(|v⟩⟨v|)) for all |v⟩ ∈ H_in → τ feasible only for the unit vectors in the support of ρ; reason: a weaker hypothesis; every f feasible on all of H_in is feasible on the support, which gives the source's statement
--   - encoding: signal states in an optimal decomposition → the members e.vector x with 0 < e.prob x of a pure ensemble e with pureAverage e = ρ and holevoValue N e = constrainedHolevo N ρ; reason: a member of weight zero is not a signal state; "optimal" means attaining χN(ρ)
--   - encoding: f the optimal dual function of (12)–(13) → τ Hermitian with χN(ρ) = H(N(ρ)) − Re Tr(τρ); reason: (12) with f = Re Tr(τ ·)
--   - encoding: vectors |φ⟩, |v_i⟩ of the input space → unit vectors (‖φ‖ = 1); reason: |φ⟩⟨φ| is meant as a state (p.4: "the minimization ranges over states |φ⟩"); ensemble members are states
--   - encoding: quantum channel (CPT map) → QAlgorithms.IsChannel (a finite Kraus family with Σ A_k†A_k = I); reason: the paper gives this operator-sum form as an equivalent characterization of finite-dimensional CPT maps (pp.2–3)
-- source:
--   Shor, Equivalence of Additivity Questions in Quantum Information Theory, arXiv:quant-ph/0305035v4, §5, pp. 11–12 (unnumbered)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_ShorAdditivityEquiv_holevoValue
import Definitions.Def_ShorAdditivityEquiv_constrainedHolevo

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P08

namespace ShorAdditivityEquiv

/-- Shor, *Equivalence of Additivity Questions in Quantum Information Theory*, arXiv:quant-ph/0305035v4, §5, pp.11–12, unnumbered: "Equality must hold in (13) for those |v⟩ which are signal
states in an optimal decomposition. This can be seen by considering the inequalities
χN(ρ) = H(N(ρ)) − Σi pi H(N(|vi⟩⟨vi|)) ≤ H(N(ρ)) − Σi pi f(|vi⟩⟨vi|) = H(N(ρ)) − f(ρ). For
equality to hold, it must hold in all the terms in the summation, which are exactly the signal
states |vi⟩."

**Formalization Note.** "An optimal decomposition" is a pure-state ensemble `e` with average
`ρ` attaining `χ_N(ρ)`; "f" is the optimal dual function of (12)–(13): `f = Re Tr(τ ·)` with `τ`
Hermitian, feasible for (13), and `χ_N(ρ) = H(N(ρ)) − f(ρ)`. Feasibility is required on the unit
vectors of the support of `ρ` only, the form of (13) in `constrainedHolevo_dual`; a `τ` feasible
on all of `H_in` is a special case. The "signal states" of the ensemble are its members of
positive weight (`0 < e.prob x`); members of weight zero are not signal states. `ρ` is any
density matrix: that it is one follows from `pureAverage e = ρ`, so it is not a separate
hypothesis (the argument does not use full rank). -/
theorem dual_tight_at_signal_states {I O : Type} [Fintype I] [DecidableEq I] [Fintype O]
    [DecidableEq O] (N : Superop I O) (hN : IsChannel N) (ρ : Matrix I I ℂ)
    (e : PureEnsemble I) (he : pureAverage e = ρ)
    (hopt : holevoValue N e = constrainedHolevo N ρ) (τ : Matrix I I ℂ) (hτ : τ.IsHermitian)
    (hfeas : ∀ v : EuclideanSpace ℂ I, ‖v‖ = 1 → v.ofLp ∈ LinearMap.range ρ.mulVecLin →
      (τ * pureDensity v).trace.re ≤ vnEntropy (N (pureDensity v)))
    (hdual : constrainedHolevo N ρ = vnEntropy (N ρ) - (τ * ρ).trace.re) :
    ∀ x, 0 < e.prob x →
      (τ * pureDensity (e.vector x)).trace.re = vnEntropy (N (pureDensity (e.vector x))) := by sorry

end ShorAdditivityEquiv
