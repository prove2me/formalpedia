-- Prove2me | Theorems.Thm_QIMAOracleSep_Separation_Supplement_lemma_4_1
-- name    : QIMAOracleSep.Separation.Supplement.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:38:04.904196+00:00
-- url     : https://prove2.me/theorems/3917ae58-2b35-465a-841c-32cd6d8856b6
-- title:
--   Lemma 4.1 — Small-phase Marriott–Watrous gadget
-- statement:
--   Let $P$ and $Q$ be orthogonal projectors on a finite-dimensional complex space, with $P\ne0$, and let $R_P=2P-I$. For $0<\theta\le1/4$ put
--   $$W_\theta=R_P\,e^{-i\theta Q}\,e^{i\theta P},\qquad E_\theta=\frac{2I+W_\theta+W_\theta^\dagger}{4},\qquad \omega=\lambda_{\max}\big(PQP|_{\operatorname{im}P}\big),$$
--   and $G_\theta(\lambda)=\tfrac12\big(1+\sqrt{1-(1-\lambda)^2\sin^2\theta}\big)$. Then:
--
--   1. $\lambda_{\max}(E_\theta)=G_\theta(\omega)$;
--   2. $G_\theta$ is increasing on $[0,1]$;
--   3. $G_\theta(2/3)-G_\theta(1/3)\ge\theta^2/72$;
--   4. $\|W_\theta-R_P\|_{\mathrm{op}}\le2\theta$.
--
--   The unit $W_\theta$ is within $2\theta$ of the exact reflection $R_P$ while its Hadamard test reproduces, monotonically, the optimal acceptance probability $\omega$ of a QMA verifier with $P$ the initialization projector and $Q$ the accepting projector. Theorems 4.2 and 4.5 build on it.
--
--   Differences from the source:
--   - encoding: e^{iθP}, e^{−iθQ} → I + (e^{iθ} − 1)P and I + (e^{−iθ} − 1)Q; reason: exact exponentials of orthogonal projectors
--   - encoding: λmax(E_θ) and ω = λmax(PQP|im P) → the supremum of Re⟨v, E_θ v⟩ over unit vectors, and of Re⟨v, Q v⟩ over unit vectors with Pv = v; reason: Rayleigh characterization of the largest eigenvalue of a Hermitian matrix
--   - encoding: ‖W_θ − R_P‖_op ≤ 2θ → ‖(W_θ − R_P)v‖² ≤ (2θ)²‖v‖² for every v; reason: the definition of the operator norm
--   - reading: G_θ is increasing on [0,1] → G_θ is strictly increasing on [0,1]; reason: the stronger reading; G_θ' > 0 on [0,1) by (52)
-- source:
--   Itay Shalit, Mark Zhandry, The Commuting Local Hamiltonian Problem: Relativized Evidence Against BQP-Hardness, STOC 2027 submission #144 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/144.pdf, Lemma 4.1, p. 34, (34)–(41); proof pp. 34–36

import Definitions.Def_QIMAOracleSep_Separation_Supplement_Spectral

set_option autoImplicit false

namespace QIMAOracleSep.Separation.Supplement

/-- Shalit--Zhandry, pinned STOC 2027 submission #144, Lemma 4.1, p. 34, (34)--(41).
Any finite dimension. The selective phases are the exact projector exponentials
`e^{iθP} = I + (e^{iθ}-1)P`, `e^{-iθQ} = I + (e^{-iθ}-1)Q`. -/
theorem lemma_4_1 {ι : Type} [Fintype ι] [DecidableEq ι]
    (P Q : Matrix ι ι ℂ) (hP : IsOrthProjector P) (hQ : IsOrthProjector Q) (hP0 : P ≠ 0)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 4) :
    let RP : Matrix ι ι ℂ := (2 : ℂ) • P - 1
    let W : Matrix ι ι ℂ := RP * phaseShift (-θ) Q * phaseShift θ P
    rayleighMax (hadamardTestOperator W) = smallPhaseG θ (compressedMax P Q) ∧
    StrictMonoOn (smallPhaseG θ) (Set.Icc 0 1) ∧
    θ ^ 2 / 72 ≤ smallPhaseG θ (2 / 3) - smallPhaseG θ (1 / 3) ∧
    OpNormLE (W - RP) (2 * θ) := by sorry

end QIMAOracleSep.Separation.Supplement
