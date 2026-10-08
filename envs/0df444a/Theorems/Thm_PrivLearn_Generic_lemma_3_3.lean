-- Prove2me | Theorems.Thm_PrivLearn_Generic_lemma_3_3
-- name    : PrivLearn.Generic.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:52.061152+00:00
-- url     : https://prove2.me/theorems/8279a522-de6e-4be5-8611-fc8995cdb8f4
-- title:
--   Lemma 3.3 — the exponential mechanism $\mathcal A^\varepsilon_q$ is ε-differentially private
-- statement:
--   Let $H$ be a finite class of hypotheses $h:X\to\{0,1\}$ and $\varepsilon>0$. For every database size $n$, the exponential mechanism $\mathcal A^{\varepsilon}_q$, which on input $z\in(X\times\{0,1\})^n$ outputs $h\in H$ with probability proportional to $\exp(\varepsilon q(z,h)/2)$, is $\varepsilon$-differentially private: for all neighboring databases $z,z'$ and every measurable set $S$ of hypotheses,
--
--   $$\Pr[\mathcal A^{\varepsilon}_q(z)\in S]\le e^{\varepsilon}\,\Pr[\mathcal A^{\varepsilon}_q(z')\in S].$$
--
--   This is the privacy half of the generic private learner (Theorem 3.4); privacy holds for every pair of neighboring databases, with no assumption on how the data were generated.
--
--   **Formalization Note.** The statement holds for every finite $H$, also the empty one (where the output law is the zero measure); the paper's $H$ is nonempty. The example set $X$ is arbitrary here.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 11, Lemma 3.3

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivLearn_Generic_ExpMech

open MeasureTheory

namespace PrivLearn.Generic

/-- Lemma 3.3 (p. 11, following McSherry–Talwar). For every finite class `H` of hypotheses and
every `ε > 0`, the exponential mechanism `A^ε_q` is `ε`-differentially private on databases of
every size `n`. -/
theorem lemma_3_3 {X : Type*} (H : Finset (X → Bool)) (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    IsDP (fun z : Fin n → X × Bool => expMech H ε z) ε := by sorry

end PrivLearn.Generic
