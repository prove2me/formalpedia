-- Prove2me | Theorems.Thm_PolySphereLP_lemma_A_5_isotropic_energy
-- name    : PolySphereLP.lemma_A_5_isotropic_energy
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:58:27.200599+00:00
-- url     : https://prove2.me/theorems/dedba882-6103-4b52-b872-1e0797a3423f
-- title:
--   Lemma A.5 — energy retained by an isotropic restriction
-- statement:
--   Let $n\ge3$, $d\ge2$ even, $T\in E_{n,d}$ and $m=\lfloor n/2\rfloor$. For $V_O=OV_0$ with $O\in O(n)$ Haar distributed, and $b_{m,d}=\binom{m+d-1}d$,
--   $$\mathbb E_O\big[\|R_{V_O}T\|_F^2\big]=\frac{b_{m,d}}{h_{n,d}}\,\|T\|_F^2. \tag{62}$$
--   Consequently there is a rotation $O\in SO(n)$ for which
--   $$\|R_{V_O}T\|_F^2\ge\frac{b_{m,d}}{h_{n,d}}\,\|T\|_F^2. \tag{63}$$
--
--   Some rotated isotropic restriction therefore retains a $b_{m,d}/h_{n,d}$ fraction of the Frobenius energy of a harmonic tensor.
--
--   **Formalization Note** The expectation holds for every Haar probability measure on $O(n)$; $h_{n,d}$ is formula (13); $OV_0$ is the real matrix $O$ viewed in $\mathbb C$ times $V_0$.
--
--   Differences from the source:
--   - encoding: O(n) Haar distributed → every μ with IsHaarProb O(n) μ; reason: uniqueness of Haar measure
--   - reading: "there is a rotation O" → there is O ∈ SO(n); reason: the stronger reading; it implies O ∈ O(n), and it holds because (28) also holds for Haar measure on SO(n) (Fact 2.3) and W_{OV₀} = U(O)W_{V₀}, so some O ∈ SO(n) attains the SO(n)-mean b_{m,d}/h_{n,d}·‖T‖²
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), Lemma A.5, p.29, eqs. (62)–(63)

import Mathlib
import Definitions.Def_PolySphereLP_hdim
import Definitions.Def_PolySphereLP_Esp
import Definitions.Def_PolySphereLP_restrictT
import Definitions.Def_PolySphereLP_V0
import Definitions.Def_PolySphereLP_IsHaarProb

namespace PolySphereLP

/-- **Lemma A.5 (Energy retained by an isotropic restriction).** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), Lemma A.5, p.29,
eqs. (62)–(63).

Let `T ∈ E_{n,d}`, `m = ⌊n/2⌋`, `V_O = O V₀` with `O ∈ O(n)` Haar distributed, and
`b_{m,d} = (m+d−1 choose d)`. Then `E_O ‖R_{V_O} T‖²_F = (b_{m,d}/h_{n,d}) ‖T‖²_F` (62), and
consequently some rotation `O ∈ SO(n)` has `‖R_{V_O} T‖²_F ≥ (b_{m,d}/h_{n,d}) ‖T‖²_F` (63).

**Formalization Note.** Standing assumptions of §2 (p.9): `n ≥ 3`, `d ≥ 2` even. `h_{n,d}` is
formula (13) (`hdim`). The expectation is over every Haar probability measure on `O(n)`
(`IsHaarProb`); `O V₀` is the real matrix `O` cast to `ℂ` times `V₀`. The rotation in (63) is
taken in `SO(n)`: this implies the reading `O ∈ O(n)`, and it holds by (28) for `K = SO(n)`. -/
theorem lemma_A_5_isotropic_energy (n d : ℕ) (hn : 3 ≤ n) (hd : 2 ≤ d) (hde : Even d)
    (T : Tensor n d) (hT : T ∈ Esp n d) :
    (∀ μ : MeasureTheory.Measure (Fin n → Fin n → ℝ),
      IsHaarProb (Matrix.orthogonalGroup (Fin n) ℝ : Set (Matrix (Fin n) (Fin n) ℝ)) μ →
      ∫ O, frobNormSq (restrictT d ((Matrix.of O).map (fun t : ℝ => (t : ℂ)) * V0 n) T) ∂μ =
        ((n / 2 + d - 1).choose d : ℝ) / (hdim n d : ℝ) * frobNormSq T) ∧
    (∃ O ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ,
      ((n / 2 + d - 1).choose d : ℝ) / (hdim n d : ℝ) * frobNormSq T ≤
        frobNormSq (restrictT d (O.map (fun t : ℝ => (t : ℂ)) * V0 n) T)) := by sorry

end PolySphereLP
