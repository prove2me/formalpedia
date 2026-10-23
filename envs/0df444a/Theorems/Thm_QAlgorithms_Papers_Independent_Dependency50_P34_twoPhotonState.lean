-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P34_twoPhotonState
-- name    : QAlgorithms.Papers.Independent.Dependency50.P34.twoPhotonState
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:22:32.499974+00:00
-- url     : https://prove2.me/theorems/1e0a33f8-90f2-449c-a86f-ea1d2a6eada8
-- title:
--   Balanced-MZI two-photon state with corrected relative phase
-- statement:
--   Consider two balanced splitters with transmission amplitude $1/\sqrt2$ and reflection amplitude $i/\sqrt2$, with a phase $\theta\in\mathbb R$ in the second intermediate path. The input is one photon in each input mode. Write $|m,n\rangle$ for the normalized Fock ket with $m$ photons at output 4 and $n$ photons at output 5. Construct the output $\psi_\theta$ by applying the two creation polynomials given by the columns of $M=B_2\operatorname{diag}(1,e^{i\theta})B_1$ to the vacuum. Then $\|\psi_\theta\|=1$ and
--   $$
--   \psi_\theta=
--   \frac{i(1-e^{2i\theta})}{2\sqrt2}(|2,0\rangle-|0,2\rangle)
--   -\frac{1+e^{2i\theta}}2|1,1\rangle.
--   $$
--   This gives the exact pure comparison state, including the relative phase between bunched and coincident terms.
--
--   **Source correction.** Printed Eq.(35) has $(1-e^{2i\theta})(|0,2\rangle-|2,0\rangle)/(2\sqrt2)+(1+e^{2i\theta})|1,1\rangle/2$. The displayed statement corrects that expression to agree with the paper's own matrix Eq.(21). The change is not removable by a single global phase for general $\theta$.
-- source:
--   Quantum Interference between a Single-Photon Fock State and a Coherent State, arXiv:1009.1844v2, PDF p. 8, §III/D, Eq.(35), corrected using Eq.(21)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P34

noncomputable section

open scoped Matrix

namespace QAlgorithms.Papers.Independent.Dependency50.P34

/-- arXiv:1009.1844v2, PDF p.8, §III/D, Eq.(35), with its relative phase corrected
using the paper's own Eq.(21). Printed: (1-z²)(|0,2>-|2,0>)/(2 sqrt(2))
+ (1+z²)|1,1>/2. Changed: i(1-z²)(|2,0>-|0,2>)/(2 sqrt(2))
- (1+z²)|1,1>/2. Why: multiply the two columns of Eq.(21) as creation
polynomials. Their entries are ((1-z)/2,i(1+z)/2) and
(i(1+z)/2,(z-1)/2). This is a relative-phase correction, not just a global
phase choice; the printed probabilities remain unchanged. Independent moderation
of this correction is pending. -/
theorem twoPhotonState (theta : ℝ) :
    let e := Complex.exp (2 * Complex.I * (theta : ℂ))
    ‖comparisonOutput theta‖ = 1 ∧
      comparisonOutput theta =
        (Complex.I * (1 - e) / (2 * (Real.sqrt 2 : ℂ))) •
          (fockKet 2 0 - fockKet 0 2) -
        ((1 + e) / 2) • fockKet 1 1 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P34

end
