-- Prove2me | Theorems.Thm_WangMinimaxRegret_Reformulation_eq_2_3
-- name    : WangMinimaxRegret.Reformulation.eq_2_3
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:35:26.044766+00:00
-- url     : https://prove2.me/theorems/e890e145-0f5c-4d46-9fd6-c209e20d2e4c
-- title:
--   Section 2, equations (2)–(3) — homogenization
-- statement:
--   Fix consistent valuation data, a payment $m\in\mathcal M$, and a finite price $p\in I$. Let $\mathcal F_0$ contain all probability laws supported on $I$ with the specified finite moments; unlike the printed ambiguity class, displayed (2) imposes no condition $F(a)=0$. Let $\mathcal H_p$ contain the finite nonnegative measures supported on $I$ with finite moments, centered moment equalities $\int(x^k-\mu_k)\,dH=0$, and tail mass $H([p,\infty))=1$. Then
--   $$\inf_{F\in\mathcal F_0,\ T_F(p)>0}\frac{\int m\,dF}{T_F(p)}=\inf_{H\in\mathcal H_p}\int m\,dH.$$
--   Moreover each positive-tail $F\in\mathcal F_0$ maps to a feasible $H=F/T_F(p)$, normalization of this $H$ recovers $F$, and $\int m\,dH=(\int m\,dF)/T_F(p)$. Conversely each $H\in\mathcal H_p$ has positive total mass, its normalization $F=H/H(I)$ lies in $\mathcal F_0$ and has positive tail, rescaling this $F$ recovers $H$, and the same objective identity holds. The equality includes infeasible-price cases through empty infima of $+\infty$. This is the measure, rather than finite-vector, version of the displayed change of variables.
--
--   Differences from the source:
--   - encoding: real interval, payment functions, probability laws, and moment orders 1 through K → real-line Borel measures supported on the interval, Stieltjes functions extended by zero below a and constantly above finite b, and Fin K exponents i+1; reason: extensions only fix values outside the domain; all atoms and payment jumps are retained, including the payment atom at a>0
--   - encoding: the seller knows moments of an actual valuation distribution → Consistent d requires a nonempty printed ambiguity class, with finite specified moments; reason: makes the standing information-consistency assumption explicit; no interiority, positive variance, or density is assumed
--   - encoding: nonnegative revenue integrals and optimization infima/suprema → nonnegative extended integrals and ENNReal/EReal extrema; zero-tail laws impose no fractional constraint; reason: avoids nonintegrable real integrals defaulting to zero and empty real extrema; empty infima are positive infinity
--   - encoding: homogeneous rows k=0,...,K and scalar rescaling of H → finite nonnegative H, integrable centered rows k=1,...,K, and a tail indicator row; reason: finite mass and finite moments make rescaling and real moment equalities meaningful; the k=0 row is redundant because mu_0=1
--   - reading: the domain [a,b], with infinity used in later applications → finite-valued valuations and prices on [a,infinity) when b=infinity; reason: retains those applications without a compact cutoff
-- source:
--   Wang, Liu and Zhang (2024), Minimax Regret Robust Screening with Moment Information, https://doi.org/10.1287/msom.2023.0072, Section 2, p. 8, equations (2)–(3)

import Definitions.Def_WangMinimaxRegret_Reformulation_Programs

open MeasureTheory Set
open scoped ENNReal NNReal
set_option autoImplicit false

namespace WangMinimaxRegret.Reformulation

theorem eq_2_3 (d : Data) (hc : Consistent d) (m : StieltjesFunction ℝ)
    (hm : IsPayment d m) (p : ℝ) (hp : p ∈ interval d) :
    fractionalValue {F | MomentLaw d F} m p = (homogenizedLP d m p).value ∧
    (∀ F : Measure ℝ, MomentLaw d F → 0 < tail F p →
      (homogenizedLP d m p).Feasible (scaleToTail F p) ∧
      normalizeMass (scaleToTail F p) = F ∧
      revenue m (scaleToTail F p) = revenue m F / tail F p) ∧
    (∀ H : Measure ℝ, (homogenizedLP d m p).Feasible H →
      0 < H univ ∧ MomentLaw d (normalizeMass H) ∧
      0 < tail (normalizeMass H) p ∧ scaleToTail (normalizeMass H) p = H ∧
      revenue m (normalizeMass H) / tail (normalizeMass H) p = revenue m H) := by sorry

end WangMinimaxRegret.Reformulation
