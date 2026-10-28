-- Prove2me | Theorems.Thm_QPurityAmp_Choi_lemma_S2_3
-- name    : QPurityAmp.Choi.lemma_S2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:24.106446+00:00
-- url     : https://prove2.me/theorems/c248cc87-48f0-47da-b3ca-fd8d89e519c0
-- title:
--   Lemma S2.3, p. 19 — P = Id − (I/d) ⊗ tr_out is an orthogonal projector on operators on V_out ⊗ V_in
-- statement:
--   Let $d\ge 1$ and let $\mathrm{in}$ be any finite-dimensional register. On the operators $X$ on $\mathbb C^d\otimes\mathrm{in}$ define
--   $$P(X)=X-\frac{\mathbb I_d}{d}\otimes\mathrm{tr}_{\mathrm{out}}X .$$
--   Then
--
--   1. $P$ is idempotent: $P(P(X))=P(X)$ for every $X$;
--   2. $P$ is self-adjoint for the Hilbert–Schmidt inner product: $\mathrm{tr}(X^\dagger P(Y))=\mathrm{tr}(P(X)^\dagger Y)$ for all $X,Y$.
--
--   So $P$ is the orthogonal projection onto the operators with $\mathrm{tr}_{\mathrm{out}}X=0$, the direction space of the affine constraint $\mathrm{tr}_{\mathrm{out}}T=\mathbb I$ of the SDP. Components of a cost matrix killed by $P$ do not change the optimization.
--
--   **Formalization Note** The paper says "a projector"; the text above the lemma defines $P=1-L^+L$, an orthogonal projection, so both idempotence and self-adjointness are stated. The text just above also writes $\mathrm{tr}^+_{\mathrm{out}}=\mathrm{tr}^\star_{\mathrm{out}}=\frac{\mathbb I}{d}\otimes\cdot$; the adjoint is in fact $\mathbb I\otimes\cdot$ and only the pseudoinverse is $\frac{\mathbb I}{d}\otimes\cdot$. This slip does not affect the lemma. The input register is a general finite type, which covers the paper's $\mathbb V^{[\varsigma]}_{\mathrm{in}}$ and the full $W^{\otimes n}$.
-- source:
--   Li, Fu, Isogawa, Silva and Chuang, Optimal Quantum Purity Amplification, arXiv:2409.18167v4, p. 19, Lemma S2.3 and the paragraph above it

import Mathlib
import Definitions.Def_QPurityAmp_Choi_OptimalChoi
noncomputable section

namespace QPurityAmp.Choi

open scoped Matrix

/-- Lemma S2.3, p. 19: P = Id − (I/d) ⊗ tr_out is a projector on the operators on
V_out ⊗ V_in: it is idempotent, and self-adjoint for the Hilbert–Schmidt inner product
⟨X, Y⟩ = tr(X† Y) (so it is the orthogonal projection onto ker tr_out). -/
theorem lemma_S2_3 {d : ℕ} [NeZero d] {ι : Type} [Fintype ι] [DecidableEq ι] :
    (∀ X : Matrix (Fin d × ι) (Fin d × ι) ℂ, projP (projP X) = projP X) ∧
      (∀ X Y : Matrix (Fin d × ι) (Fin d × ι) ℂ,
        (Xᴴ * projP Y).trace = ((projP X)ᴴ * Y).trace) := by sorry

end QPurityAmp.Choi
