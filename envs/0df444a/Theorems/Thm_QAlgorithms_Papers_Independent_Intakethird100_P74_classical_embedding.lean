-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P74_classical_embedding
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P74.classical_embedding
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:10:11.780484+00:00
-- url     : https://prove2.me/theorems/3acb7213-a3d3-42d7-956d-5b3271e47e01
-- title:
--   Classical wiretap embedding, Kraus family and dilation recovery
-- statement:
--   Let $X,Y,Z$ be finite classical alphabets with $X$ nonempty, and suppose $p(y,z\mid x)\ge0$ and $\sum_{y,z}p(y,z\mid x)=1$ for every $x$. Embed the symbols as orthonormal quantum basis vectors. Define
--
--   $$
--   \mathcal N_C(\rho)=\sum_{x,y,z}\langle x|\rho|x\rangle p(y,z\mid x)
--    |y,z\rangle\langle y,z|,
--   \qquad K_{xyz}=\sqrt{p(y,z\mid x)}|y,z\rangle\langle x|.
--   $$
--
--   The family $\{K_{xyz}\}$ is normalized, $\sum_{xyz}K_{xyz}^\dagger K_{xyz}=I$, and defines a CPTP map. The explicit map
--
--   $$
--   V|\psi\rangle=\sum_{x,y,z}\sqrt{p(y,z\mid x)}\langle x|\psi\rangle
--    |y,z\rangle^{BE}|x,y,z\rangle^{S_2}
--   $$
--
--   is an isometry. For every normalized density matrix $\rho$,
--
--   $$
--   \sum_{xyz}K_{xyz}\rho K_{xyz}^\dagger
--   =\mathcal N_C(\rho)
--   =\operatorname{Tr}_{S_2}(V\rho V^\dagger).
--   $$
--
--   This embeds a general finite classical wiretap channel, discarding off-diagonal input entries while keeping the dilation record in a shield unavailable to Eve.
-- source:
--   Polar codes for private classical communication, arXiv:1203.5794v1, PDF p. 6, Appendix A, unnumbered: classical wiretap embedding and explicit dilation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P74

namespace QAlgorithms.Papers.Independent.Intakethird100.P74

open QAlgorithms

open scoped ComplexConjugate Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {B E S1 S2 : Type}

variable [Fintype B] [Fintype E] [Fintype S1] [Fintype S2]

variable [DecidableEq B] [DecidableEq E] [DecidableEq S1] [DecidableEq S2]

/-- PDF p.6, Appendix A: for arbitrary finite classical alphabets, the printed Kraus
operators are normalized, their channel is Eq.(14), the explicit dilation is isometric,
and tracing its shield recovers Eq.(14) on every normalized input state. -/
theorem classical_embedding {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [Nonempty X]
    (p : X → Y → Z → ℝ) (hp : ∀ x y z, 0 ≤ p x y z)
    (hnorm : ∀ x, ∑ y, ∑ z, p x y z = 1) :
    IsKrausFamily (classicalKraus p) ∧
    IsChannel (classicalEmbedding p) ∧
    (classicalDilation p)ᴴ * classicalDilation p = 1 ∧
    (∀ rho : Matrix X X ℂ, IsDensityMatrix rho →
      krausApply (classicalKraus p) rho = classicalEmbedding p rho ∧
      traceRight (classicalDilation p * rho * (classicalDilation p)ᴴ) =
        classicalEmbedding p rho) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P74
