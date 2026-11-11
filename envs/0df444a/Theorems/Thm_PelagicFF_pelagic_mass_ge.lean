-- Prove2me | Theorems.Thm_PelagicFF_pelagic_mass_ge
-- name    : PelagicFF.pelagic_mass_ge
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:55:51.132631+00:00
-- url     : https://prove2.me/theorems/128633f3-4373-4a46-b18a-0957af6b334f
-- title:
--   §4.1, p.28 — the Pelagic outputs carry squared Fourier mass at least $3/4$
-- statement:
--   Let $h:\{0,1\}^n\to\{-1,1\}$. Then the frequencies satisfying the Pelagic condition (9) carry at least three quarters of the squared Fourier mass:
--   $$\sum_{y:\ h\text{ satisfies (9) at }y}\ \widehat h(y)^2\ \ge\ 1-\frac18-\frac18=\frac34 .$$
--
--   Since measuring the state $\sum_y\widehat h(y)|y\rangle$ returns $y$ with probability $\widehat h(y)^2$, this is the success guarantee of the quantum protocol; in particular $\mathrm{PFF}_n$ is total.
--
--   **Formalization Note** $h$ is `sign ∘ H` for a `Bool`-valued `H`.
--
--   Differences from the source:
--   - encoding: Boolean functions with values in {−1,1} → Bool-valued functions read through OAI.Cotype.sign (false ↦ 1, true ↦ −1); reason: a bijection of value sets; same instances
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), §4.1, p.28

import Mathlib
import Definitions.Def_PelagicFF_PFF

open OAI.Cotype
open Classical

namespace PelagicFF

/-- **The Pelagic mass bound (§4.1, p.28).** For every Boolean function `h : {0,1}ⁿ → {−1,1}`, the
total squared Fourier mass of the frequencies `y` satisfying the Pelagic condition (9) is at least
`1 − 1/8 − 1/8 = 3/4`.

arXiv:2610.05585 (held version, sha256 4564aef3…), §4.1, p.28: "The total squared Fourier mass of
all y which satisfy both inequalities is therefore at least 1 − 1/8 − 1/8 = 3/4."

**Formalization Note.** `h` is `sign ∘ H` for a `Bool`-valued `H`; the Fourier coefficient is
`OAI.Cotype.fourier`. -/
theorem pelagic_mass_ge (n : ℕ) (H : (Fin n → Bool) → Bool) :
    (3 : ℝ) / 4 ≤ ∑ y ∈ Finset.univ.filter (fun y => IsPelagic (fun x => sign (H x)) y),
      OAI.Cotype.fourier (fun x => sign (H x)) y ^ 2 := by sorry

end PelagicFF
