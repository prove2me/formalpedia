-- Prove2me | Theorems.Thm_PSPACEOracleSynth_Main_Supplement_lemma_7_2
-- name    : PSPACEOracleSynth.Main.Supplement.lemma_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:39:07.464086+00:00
-- url     : https://prove2.me/theorems/d3ac28d6-a000-4897-9fcf-96bdd0170b5b
-- title:
--   Lemma 7.2 — Exact adaptive injection of any Boolean phase unitary after ℓ+1 resource states, on every outcome sequence.
-- statement:
--   Let $f_0$ be any Boolean function on $\ell$ bits. One injection of $|\varphi_f\rangle$ into an $\ell$-qubit register $X$ applies a CNOT from each qubit of $X$ onto the corresponding qubit of a resource register holding $|\varphi_f\rangle$ and measures the resource; its branch at outcome $v$ is the operator $K_{f,v}$ on $X$ with $\langle w|K_{f,v}|u\rangle=\sum_c\langle w,v|\mathrm{CNOT}|u,c\rangle\,\varphi_f(c)$. Inject $|\varphi_{f_0}\rangle,\ldots,|\varphi_{f_\ell}\rangle$ in this order, where $f_{j+1}=\partial_{v_j}f_j$ and $v_j$ is the outcome of the injection of $|\varphi_{f_j}\rangle$. For every sequence of outcomes $v_0,\ldots,v_\ell$,
--
--   $$K_{f_\ell,v_\ell}\cdots K_{f_0,v_0}=(2^{-\ell/2})^{\ell+1}\,Z_{f_0},$$
--
--   that is, the injections apply $Z_{f_0}$ to $X$ on every outcome sequence (each outcome having amplitude $2^{-\ell/2}$). The equality retains global phase and acts on every input, including inputs entangled with further registers. It also covers $\ell=0$.
--
--   Differences from the source:
--   - encoding: the injections apply Z_{f0} to X for all outcomes → the product of the l+1 subnormalized injection branch operators, built from CNOT and the phase state, equals (2^(-l/2))^(l+1) • Z_{f0}; reason: each branch carries the outcome amplitude 2^(-l/2), a positive real; matrix equality is the action on every input and further register
--   - encoding: finite qubit registers and normalized states → Bits n, UnitKet and density-matrix predicates, including n=0; reason: basis labels and explicit state predicates change no instance
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1740.pdf, Lemma 7.2, p. 38

import Mathlib
import Definitions.Def_PSPACEOracleSynth_Main_Supplement_Injection

open QAlgorithms QAlgorithms.Complexity
open scoped Matrix ComplexOrder Kronecker ENNReal
noncomputable section

namespace PSPACEOracleSynth.Main.Supplement


/-- Lemma 7.2, p. 38: for every sequence of ℓ+1 outcomes, the composed injection branches act on X
as Z_{f₀}, times the outcome amplitude (2^{−ℓ/2})^{ℓ+1}, a positive real; no phase is removed.
Matrix equality asserts the action on every input, with any further register. -/
theorem lemma_7_2 (l : ℕ) (f : Bits l → Bool) (v : List (Bits l))
    (hlen : v.length = l+1) :
    injectionRun f v = (((Real.sqrt ((2 : ℝ)^l))⁻¹ ^ (l+1) : ℝ) : ℂ) • phase f := by sorry

end PSPACEOracleSynth.Main.Supplement
