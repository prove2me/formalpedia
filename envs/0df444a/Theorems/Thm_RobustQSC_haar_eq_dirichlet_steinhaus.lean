-- Prove2me | Theorems.Thm_RobustQSC_haar_eq_dirichlet_steinhaus
-- name    : RobustQSC.haar_eq_dirichlet_steinhaus
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:53:52.327321+00:00
-- url     : https://prove2.me/theorems/da922443-ad49-4f88-8afc-f245d4dd9a34
-- title:
--   §2.5.3, p.15 — Haar law as $\mathrm{Dirichlet}(\vec 1)$ moduli with independent Steinhaus phases
-- statement:
--   A Haar-random unit vector $f:\{0,1\}^n\to\mathbb C$ has the law of
--
--   $$
--   f(x)=\sqrt{\mu(x)}\,\omega_x,\qquad\mu\sim\mathrm{Dirichlet}(\vec1),\quad(\omega_x)_x\ \text{i.i.d. Steinhaus, independent of }\mu.
--   $$
--
--   This is the fact behind stratifying $f$ by its measure: the Haar law is the mixture over $\mu\sim\boldsymbol\mu$ of the uniform laws on $F_\mu=\{f:\mu_f=\mu\}$. It is how bounds under $\mu\sim\boldsymbol\mu$ and $f\sim F_\mu$ transfer to a Haar-random $f$ in §8.
--
--   Differences from the source:
--   - reading: the stratification is described in prose, and the mixture is used without a separate statement → the identity of the two laws; reason: it is the precise content the paper uses when it passes between Haar $f$ and $f\sim F_\mu$ with $\mu\sim\boldsymbol\mu$
--   - encoding: $f$ Haar-random with $\|f\|_2=1$ → the published `haarTargetLaw`, the law of a normalized standard complex Gaussian vector; reason: the unitarily invariant probability on the unit sphere
--   - encoding: conditioning on $\mu_f=\mu$ → the image of a product law; reason: the conditioning event is null; the product form states the same mixture
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), §2.5.3, p.15; Lemma 1, p.19; glossary, p.79; used in §8, pp.73–74

import Definitions.Def_RobustQSC_dirichletOne
import Definitions.Def_RobustQSC_phaseLaw
import Definitions.Def_QAlgorithms_Defs_HaarTargetStates

namespace RobustQSC

open QAlgorithms QAlgorithms.TwoBasisCertification MeasureTheory

/-- **§2.5.3, stratification of the Haar law (p.15).** A Haar-random unit vector
`f : {0,1}ⁿ → ℂ` has the law of `f(x) = √μ(x)·ω_x` with `μ ∼ Dirichlet(1⃗)` and, independently,
`(ω_x)_x` i.i.d. Steinhaus: the Haar law is the mixture over `μ ∼ 𝛍` of the laws `F_μ`.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles for
total influence*, arXiv:2607.27184 (sha256 09d2692e…), §2.5.3, p.15 ("stratify the f's by their measure; i.e., define F_µ = {f : µ_f =
µ}. Then, for each 'typical' µ, repeat the win-win argument from the phase-state case, using the
randomness in f ∼_unif F_µ"); Lemma 1, p.19 (`µ ∼ Dirichlet(1⃗)`); glossary, p.79; used in §8,
pp.73–74.

**Formalization Note.** `haarTargetLaw` is the published law of `g/‖g‖`, `g` a standard complex
Gaussian vector. The mixture is written as the image of the product law
`Dirichlet(1⃗) ⊗ Steinhaus^{⊗N}` (not as a `bind` over `μ`). -/
theorem haar_eq_dirichlet_steinhaus (n : ℕ) :
    haarTargetLaw n =
      ((dirichletOne (Qubits n)).prod (Measure.pi fun _ : Qubits n => steinhaus)).map
        fun p => WithLp.toLp 2 fun x => ((Real.sqrt (p.1 x) : ℝ) : ℂ) * p.2 x := by sorry

end RobustQSC
