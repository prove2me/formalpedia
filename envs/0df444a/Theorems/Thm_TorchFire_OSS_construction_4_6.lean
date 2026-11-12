-- Prove2me | Theorems.Thm_TorchFire_OSS_construction_4_6
-- name    : TorchFire.OSS.construction_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:36:51.856481+00:00
-- url     : https://prove2.me/theorems/84258716-0340-4faa-82d6-9206ec8cfd52
-- title:
--   Construction 4.6 and (8) — the preparation circuit outputs $|0^n\rangle\otimes2^{-r/2}\sum_y|y\rangle|W_y\rangle$
-- statement:
--   Fix an oracle sample of Construction 4.2 ($\pi$, full-rank $A_y$, $b_y$). On registers $X,Y,U$ of $n,r,k$ qubits, apply $H^{\otimes n}$ to $X$, query $P$ from $X$ to $YU$, and query $P^{-1}$ from $YU$ to $X$. Then the output on $|0^n\rangle_X|0^r\rangle_Y|0^k\rangle_U$ is
--   $$|0^n\rangle_X\otimes2^{-r/2}\sum_{y\in\{0,1\}^r}|y\rangle_Y|W_y\rangle_U,$$
--   and measuring $Y$ gives
--   $$\Pr[Y=y]=2^{-r},\qquad\rho_{U|Y=y}=|W_y\rangle\langle W_y|\quad(8).$$
--   In the Lean statement the second part is written for the unnormalized branch: its trace is $2^{-r}$ and it equals $2^{-r}|W_y\rangle\langle W_y|$.
--
--   This is the key-generation step of every one-shot signature in the mission: it shows that $\mathrm{OSS.GenQKey}$ outputs a uniform key with its coset state.
--
--   Differences from the source:
--   - encoding: the construction for λ ≥ 2 → every parameter at max(λ, 2); reason: paper.md decision 7; equal for λ ≥ 2, and negligibility ignores finitely many λ
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Construction 4.6 and (8), p.20

import Mathlib
import Definitions.Def_TorchFire_OSS_prepCircuit

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model

namespace TorchFire.OSS

/-- **Construction 4.6 and (8)**, p.20 (Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593; [SZ25, Construction 31]).
For every oracle sample of Construction 4.2, the circuit `H^{⊗n}_X`, "Query `P` from `X` to `YU`",
"Query `P⁻¹` from `YU` to `X`" maps `|0^n⟩_X |0^r⟩_Y |0^k⟩_U` to
`|0^n⟩_X ⊗ 2^{−r/2} Σ_{y ∈ {0,1}^r} |y⟩_Y |W_y⟩_U`, and measuring `Y` gives `Pr[Y = y] = 2^{−r}` with
post-measurement state `ρ_{U|Y=y} = |W_y⟩⟨W_y|` (the unnormalized branch is `2^{−r} |W_y⟩⟨W_y|`). -/
theorem construction_4_6 (lam : ℕ) (ω : OneSample lam) :
    prepOutput ω = (fun s => if s.1 = 0 then
        (((Real.sqrt 2 : ℝ) : ℂ) ^ r lam)⁻¹ * cosetState ω s.2.1 s.2.2 else 0) ∧
    ∀ y : Bits (r lam), (Matrix.trace (block (genQKeyCQ ω) y)).re = (2 : ℝ)⁻¹ ^ r lam ∧
      block (genQKeyCQ ω) y = ((2 : ℂ)⁻¹ ^ r lam) • ketbra (cosetState ω y) := by sorry

end TorchFire.OSS
