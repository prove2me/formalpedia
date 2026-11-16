-- Prove2me | Theorems.Thm_QMomentMatch_FirstBound_Supplement_lemma_4_8
-- name    : QMomentMatch.FirstBound.Supplement.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:42:49.982481+00:00
-- url     : https://prove2.me/theorems/650f1d7a-7a3e-4966-bd53-2a20b146d998
-- title:
--   Lemma 4.8 — singleton case: $|d_\ell(\mathbf w)|\le C^\ell T^{1+\alpha_\ell}/N$ for $\mathbf w\in\{0,1\}^{m-1}$
-- statement:
--   Setting (§4.1, p. 24). Fix integers $A\ge1$, $N\ge1$ and $T\ge0$ and a quantum algorithm $\mathcal A$ making $T$ standard queries to $f:[N]\to[N]$, with acceptance probability $p(f)=\Pr[\mathcal A^f=1]$. Let $S=\{0\}\cup[A]$, $m=\lfloor N/2\rfloor$, and for $\mathbf z\in S^m$ let $h(\mathbf z)=\mathbb E_{f\sim\mathcal D_{\mathbf c(\mathbf z)}}[p(f)]$, where $\mathbf c(\mathbf z)$ is the frequency vector of step 2 of Definition 2.1. For $\mathbf w\in S^{m-1}$ put $q_{\mathbf w}(s)=h(\mathbf w,s)$ and let $d_\ell(\mathbf w)=\sum_{s=0}^{\ell}(-1)^{\ell-s}\binom\ell s q_{\mathbf w}(s)$ be its Newton coefficients (20). Let $\alpha_\ell=1-2^{1-\ell}$.
--
--   There is an absolute constant $C>0$ with the following property. Suppose $N\ge8A$, $T\ge1$ and $T^2\le N/8$, and let $2\le\ell\le A$ satisfy $T\le N^{\alpha_\ell/(1+\alpha_\ell)}$. Then for every $T$-query algorithm and every $\mathbf w\in\{0,1\}^{m-1}$,
--   $$|d_\ell(\mathbf w)|\le C^\ell\,\frac{T^{1+\alpha_\ell}}{N}.$$
--
--   This handles the singleton branch in the proof of Lemma 4.9, where every sampled multiplicity is $0$ or $1$.
--
--   **Formalization Note** "$C$ is an absolute constant" is the existential $\exists C>0$ placed before $N,A,T,\ell$, the algorithm and $\mathbf w$.
--
--   Differences from the source:
--   - encoding: a T-query quantum algorithm on f : [N] → [N] → QueryAlg (Fin N) (ZMod N) W T with any finite workspace W, any unitaries and start state, any output map out, standard oracle xorOracle f; reason: the base mission's algorithm model (theorem_2_5); [N] is Fin N for positions and ZMod N for labels
--   - encoding: S = {0} ∪ [A], w ∈ S^{m−1}, (w, s), m = ⌊N/2⌋ → Fin (A + 1), w : Fin (N / 2 - 1) → Fin (A + 1), appendLast w s, N / 2; reason: same conventions as the base definitions; s is placed in the last coordinate as on p. 18
--   - encoding: C is an absolute constant → ∃ C : ℝ, 0 < C placed before N, A, T, ℓ, the algorithm and w; reason: absolute means independent of every other quantity; requiring C > 0 loses nothing since enlarging to 1 + |C| preserves the bound
--   - encoding: an integer ℓ with 2 ≤ ℓ ≤ A → ℓ : Fin (A + 1) with 2 ≤ (ℓ : ℕ); reason: Fin (A + 1) carries ℓ ≤ A; ℓ is also a value of S as needed for the completion (w, ℓ)
-- source:
--   Chandrima Kayal, Frédéric Magniez, Sayantan Sen, Dániel Szabó, STOC 2027 submission #564 (October 2026), Lemma 4.8, pp. 31–32 (setting §4.1, p. 24)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QMomentMatch_FirstBound_Basic
import Definitions.Def_QMomentMatch_FirstBound_InducedDist
import Definitions.Def_QMomentMatch_FirstBound_Supplement_NewtonCoeff

namespace QMomentMatch.FirstBound.Supplement

open QAlgorithms QMomentMatch.FirstBound

/-- Lemma 4.8, pp. 31–32 (singleton case), in the setting of §4.1 (p. 24): a `T`-query algorithm
on `f : [N] → [N]`, `m = ⌊N/2⌋`, `S = {0} ∪ [A]`, `d_ℓ(w)` of eq. (20). `C` is absolute: it is
chosen before every other quantity. -/
theorem lemma_4_8 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N A T : ℕ) [NeZero N] (ℓ : Fin (A + 1)),
        8 * A ≤ N → 1 ≤ T → (T : ℝ) ^ 2 ≤ (N : ℝ) / 8 → 2 ≤ (ℓ : ℕ) →
        (T : ℝ) ≤ (N : ℝ) ^ (alpha ℓ / (1 + alpha ℓ)) →
        ∀ (W : Type) [Fintype W] [DecidableEq W] (alg : QueryAlg (Fin N) (ZMod N) W T)
          (out : (Fin N × ZMod N) × W → Bool) (w : Fin (N / 2 - 1) → Fin (A + 1)),
          (∀ i, (w i : ℕ) ≤ 1) →
          |newtonW alg out w ℓ| ≤ C ^ (ℓ : ℕ) * (T : ℝ) ^ (1 + alpha ℓ) / N := by sorry

end QMomentMatch.FirstBound.Supplement
