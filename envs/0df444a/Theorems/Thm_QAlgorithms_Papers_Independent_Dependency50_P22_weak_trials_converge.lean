-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P22_weak_trials_converge
-- name    : QAlgorithms.Papers.Independent.Dependency50.P22.weak_trials_converge
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:24:34.134468+00:00
-- url     : https://prove2.me/theorems/5caa43bd-648c-4272-a628-d0ffd3daf464
-- title:
--   Explicit finite LOCC instruments converge to the witness
-- statement:
--   On two qubits, for $0<\epsilon\le1$ let $M_0=\operatorname{diag}(\sqrt{1-\epsilon},1)$ and $M_1=\operatorname{diag}(\sqrt\epsilon,0)$. Each party measures with these operators and broadcasts its outcome. The parties repeat a joint trial only after outcome $00$, and stop after at most $\nu\ge1$ trials. Let $\mathcal J_\nu(\epsilon)$ retain the final joint label $00,01,10,11$. It has an implementation with at most $2\nu$ communication rounds.
--
--   Let $\mathcal J$ be the instrument in Eqs.(10)–(12), and let $\mathcal J_{\rm pad}=(\mathcal E_{00},\mathcal E_{01},\mathcal E_{10},0)$. For every real $c$ with $0<c<1$,
--   $$
--   \lim_{\nu\to\infty}D_\diamond\bigl(\mathcal J_\nu(\nu^{-c}),\mathcal J_{\rm pad}\bigr)=0.
--   $$
--   The diagonal sequence may start at $\nu=2$. Its members are independent approximation protocols because their weak-measurement parameter changes with $\nu$. This establishes the operational approximation of the target without identifying those protocols as linked prefixes.
-- source:
--   Everything You Always Wanted to Know About LOCC (But Were Afraid to Ask), arXiv:1210.4583v2, PDF p. 12, §4.1, Eqs.(13)–(19)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P22

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Dependency50.P22

open QAlgorithms.Papers.Independent.Information100.P27 (Config)

/-- PDF pp.11–12, §4.1: each nu-trial protocol needs at most 2nu broadcasts;
for every 0<c<1 the independently chosen epsilon=nu^(-c) protocols converge
in QC diamond distance to the zero-padded target. Starting at nu=2 keeps epsilon in (0,1). -/
theorem weak_trials_converge :
    (∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 → ∀ nu : ℕ, 0 < nu →
      InRounds (fun _ : Fin 2 => 2) (2 * nu) (trialInstrument epsilon nu)) ∧
    ∀ c : ℝ, 0 < c → c < 1 →
      Filter.Tendsto (fun n : ℕ => instrumentDistance
        (trialInstrument (Real.rpow (n + 2 : ℝ) (-c)) (n + 2)) paddedWitness)
        Filter.atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P22

end
