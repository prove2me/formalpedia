-- Prove2me | Theorems.Thm_TFIMPhaseDiagram_Classical_prop_16
-- name    : TFIMPhaseDiagram.Classical.prop_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:05:50.554211+00:00
-- url     : https://prove2.me/theorems/ddeb728d-4c86-4dbe-8725-bed93b66ca40
-- title:
--   Proposition 16 — Positive partition estimator with approximate sampling and all resource clauses
-- statement:
--   Let $\nu$ be a probability measure on an arbitrary measurable space $\Omega$, let $L\ge1$ be an integer, and let $V:\Omega\to[-L,L]$ be measurable. Put $\mu_\lambda=T_{\lambda V}\nu$ and $Z(\lambda)=\mathbb E_\nu e^{\lambda V}$. For every $\epsilon,\delta\in(0,1)$ a uniform oracle Real RAM program outputs a strictly positive estimator satisfying
--   $$\Pr[(1-\epsilon)Z(1)\le\widehat Z\le(1+\epsilon)Z(1)]\ge1-\delta.$$
--   It uses $K'=Kr$ independent sample calls and $K'$ evaluations of $V$, with $K=L\lceil16e^2L/\epsilon^2\rceil$ and $r=2\lceil16\log(1/\delta)\rceil+1$, and at most $aK'$ additional operations for one absolute constant $a$. Each draw comes from the prescribed stage $i/L$, $0\le i<L$, with TV error at most $1/(8K)$. This preserves $K=\Theta((L/\epsilon)^2)$ and $K'=\Theta(K\log(1/\delta))$ in the usual small-failure asymptotic regime. Stage selection is deterministic and the sampling tape is independent.
--
--   This is the source's general sampling-to-counting reduction, without restricting $\Omega$ to a finite set.
--
--   Differences from the source:
--   - encoding: K=Theta((L/epsilon)^2), Kprime=Theta(K log(1/delta)), O(Kprime) work → K=L ceil(16 exp(2)L/epsilon^2), r=2 ceil(16 log(1/delta))+1, Kprime=Kr, and a uniform charged oracle program; reason: These are the proof sample count and a derived valid odd median witness. Integer ceilings retain every delta in (0,1); the stated logarithmic order is asymptotic as delta tends to zero.
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026), canonical source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, printed p.9 = PDF p.9, Proposition 16

import Definitions.Def_TFIMPhaseDiagram_Classical_annealing

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

namespace TFIMPhaseDiagram.Classical
/-- Proposition 16, p.9; arbitrary sample spaces, approximate independent oracle draws,
positive output, both error inequalities, and all three resource counts. -/
theorem prop_16 : ∃ (P : OracleProgram) (a : ℕ), OracleAdmissible P ∧ 0 < a ∧
  ∀ (A : Type) (mA : MeasurableSpace A) (ν : Measure A), IsProbabilityMeasure ν →
  ∀ (L : ℕ), 1 ≤ L → ∀ (V : A → ℝ), Measurable V → (∀ x, |V x| ≤ (L : ℝ)) →
  ∀ (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 →
  ∀ (approx : Fin L → Measure A), (∀ i, IsProbabilityMeasure (approx i)) →
  (∀ i, tv (approx i) (tilt ν (fun x => (i.val / (L : ℝ))*V x)) ≤
    1/(8*(baseSamples L ε : ℝ))) →
  let K' := totalSamples L ε δ
  let input := [(L : ℝ), ε, δ]
  let out := oracleOutput (L := L) P V input (a*K')
  (∀ ω : ℕ → Fin L → A, ∃ t, t+1 ≤ a*K' ∧
    let s := oracleState P V input ω t
    oracleHalted P s ∧ s.samples = K' ∧ s.evaluations = K' ∧ s.arithmetic ≤ a*K') ∧
  PrescribedStages (L := L) P V input (productSamples L ε) (a*K') ∧
  Measurable out ∧
  (∀ ω, 0 < out ω) ∧
  1-δ ≤ (oracleTapeLaw approx).real {ω |
    (1-ε)*(∫ x, Real.exp (V x) ∂ν) ≤ out ω ∧
    out ω ≤ (1+ε)*(∫ x, Real.exp (V x) ∂ν)} := by sorry
end TFIMPhaseDiagram.Classical
