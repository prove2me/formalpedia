-- Prove2me | Theorems.Thm_QuantumStateIdentity321_Schur_Supplement_theorem_5_1
-- name    : QuantumStateIdentity321.Schur.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:00:28.887516+00:00
-- url     : https://prove2.me/theorems/a5c0fa11-ebe1-4314-b937-02be559743e1
-- title:
--   Theorem 5.1 — for $\alpha\le\frac12\arccos\sqrt{1-\varepsilon}$, Problem 1 is a special case of $\mathrm{QSI}^\varepsilon_n$
-- statement:
--   Let $n\ge2$, $\varepsilon\in[0,1/2)$, and let $\alpha\in[0,\pi/2]$ with
--
--   $$
--   \alpha\le\tfrac12\arccos\sqrt{1-\varepsilon}.
--   $$
--
--   Then Problem 1 with angle $\alpha$ is a special case of $\mathrm{QSI}^\varepsilon_n$: for every $\theta\in[0,2\pi)^n$,
--
--   1. the yes inputs $|\psi_{\theta_1}\rangle,\dots,|\psi_{\theta_n}\rangle$ are unit vectors and form a yes instance ($|\langle\psi_{\theta_i}|\psi_{\theta_j}\rangle|^2\ge1-\varepsilon$ for $i\ne j$);
--   2. for every $i\in[n]$, the no inputs, with the $i$-th state replaced by $|\varphi_{\theta_i}\rangle$, are unit vectors and form a no instance (some pair has fidelity at most $\varepsilon$).
--
--   Hence every algorithm for $\mathrm{QSI}^\varepsilon_n$ solves Problem 1, and lower bounds for Problem 1 transfer to $\mathrm{QSI}^\varepsilon_n$.
--
--   Differences from the source:
--   - encoding: "Problem 1 is a special case of QSI^ε_n" → the two inclusions (yes inputs are unit yes instances, no inputs are unit no instances) for every θ ∈ [0, 2π)ⁿ and i; reason: this is what "special case" means here
--   - encoding: indices $1,\dots,n$ → `Fin n`, label $i$ is the source's $i+1$; reason: Lean convention; same instances
-- source:
--   Shih-Han Hung, Ming-Hsien Tsai, STOC 2027 submission #321 (October 2026), Theorem 5.1, PDF/printed p.18, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/321.pdf

import Definitions.Def_QuantumStateIdentity321_Schur_Supplement_LowerBound

namespace QuantumStateIdentity321.Schur.Supplement

open Matrix

/-- Theorem 5.1, p.18: for `n ≥ 2`, `ε ∈ [0, 1/2)` and an angle `α ∈ [0, π/2]` with
`α ≤ ½ arccos √(1 − ε)`, Problem 1 is a special case of `QSI^ε_n`: for every `θ ∈ [0, 2π)ⁿ` the
yes inputs `|ψ_{θ₁}⟩, …, |ψ_{θₙ}⟩` are unit vectors forming a yes instance, and for every `i` the
no inputs (coordinate `i` replaced by `|φ_{θᵢ}⟩`) are unit vectors forming a no instance. -/
theorem theorem_5_1 (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2) (α : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ Real.pi / 2) (hα : α ≤ problem1Angle ε)
    (θ : Fin n → ℝ) (hθ : IsPhaseVector θ) :
    ((∀ j, ‖yesInput α θ j‖ = 1) ∧ IsYesInstance ε (yesInput α θ)) ∧
      ∀ i : Fin n, (∀ j, ‖noInput α θ i j‖ = 1) ∧ IsNoInstance ε (noInput α θ i) := by sorry

end QuantumStateIdentity321.Schur.Supplement
