-- Prove2me | Theorems.Thm_TaylorHGAudit_PEP_exact_sdp_performance
-- name    : TaylorHGAudit.PEP.exact_sdp_performance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:53:19.242341+00:00
-- url     : https://prove2.me/theorems/7b23841c-3cc7-4ef6-ae94-51d4fd239d78
-- title:
--   Theorem 5 — exact SDP performance including nonsmooth functions
-- statement:
--   Fix $N\ge0$, $0\le\mu<L\le+\infty$ with finite $\mu$, $R\ge0$, a fixed-step coefficient table $H\in\mathbb R^{N\times N}$, $b\in\mathbb R^{N+1}$, and symmetric $C\in\mathbb S^{N+2}$. For every dimension $d\ge N+2$,
--
--   $$\boxed{w^{(d)}_{\mu,L}(R,H,N,\mathcal P_{b,C})
--   =w^{\rm sdp}_{\mu,L}(R,H,N,b,C).}$$
--
--   On the left, the supremum ranges over actual proper closed extended-valued functions $F\in\mathcal F_{\mu,L}(\mathbb R^d)$, finite-valued minimizers, and actual admissible fixed-step oracle runs starting within distance $R$. Their criterion is $\mathcal P_{b,C}=b^\top(v-v_*\mathbf1)+\operatorname{Tr}(CP^\top P)$ with $P=[g_0\ \cdots\ g_N\ x_0-x_*]$.
--
--   On the right, $G\in\mathbb S^{N+2}$ and $v\in\mathbb R^{N+1}$ are independent variables, extended by $v_*=0$, with the explicit constraints $G\succeq0$, $v_j-v_i+\operatorname{Tr}(GA_{ij})\le0$ for all $i,j\in\{0,\ldots,N,*\}$, and $\operatorname{Tr}(GA_R)\le R^2$. The reciprocal matrices are those defined in the SDP item. Both values are extended-real suprema; no finite value or attaining instance is asserted.
--
--   This identifies the full worst-case optimization problem with the stated semidefinite program. It includes $N=0$, $R=0$, zero step tables and $L=+\infty$, without a correspondence hypothesis or a rank assumption in the independent SDP.
--
--   Differences from the source:
--   - encoding: finite nonnegative curvature and extended positive smoothness on Euclidean space → NNReal curvature, ENNReal smoothness, EReal function values and real-height epigraph convexity; reason: the strict parameter hypothesis excludes zero smoothness and preserves every source instance, including infinite smoothness; only finite quadratic values are subtracted
--   - reading: p. 13 quotient coefficients such as L/(L−μ) while Theorem 5 includes L = +∞ → q = 1/L and a = 1/(1−μq), with coefficient tuple (a,qa,μqa,μa); reason: finite-L algebra agrees identically and the infinite-L tuple (1,0,0,μ) agrees with (4) and Corollary 2
--   - reading: gradient-oracle notation alongside the explicit nonsmooth case and subgradient interpolation → all admissible subgradient responses are quantified independently at the query points; reason: this retains the nonsmooth interpolation interpretation, including repeated minimizers with nonzero selected responses, while the star marker may use zero
--   - encoding: normalized iterates and values x_* = 0, f_* = 0 in (d-PEP) → actual minimizers with finite v_* and normalized differences v_i−v_* and x_0−x_* in the criterion; reason: translation and additive shifts change no normalized performance; no correspondence or normalization identity is assumed
--   - encoding: N steps, N+1 values, N+2 Gram columns and d ≥ N+2 → Fin N coefficient matrix, Fin (N+1) oracle data, Fin (N+2) matrices and N+2 ≤ d; reason: the coefficient mask implements h_i,k = 0 for k ≥ i, so arbitrary unused entries are ignored; Option adds the distinct star index and no natural subtraction is used
--   - encoding: a norm radius and possibly unbounded suprema over real performance values → R ≥ 0 including zero and two independent EReal suprema, with PosSemidef including symmetry; reason: the source norm radius is nonnegative; extended suprema preserve infinity and do not assert attainment or finiteness
-- source:
--   Taylor, Hendrickx & Glineur, arXiv:1502.05666v6, Theorem 5, p. 14 (PDF 14), https://arxiv.org/abs/1502.05666v6

import Mathlib
import Definitions.Def_TaylorHGAudit_PEP_Class
import Definitions.Def_TaylorHGAudit_PEP_Run
import Definitions.Def_TaylorHGAudit_PEP_SDP

namespace TaylorHGAudit.PEP

theorem exact_sdp_performance {N : ℕ} (μ : NNReal) (L : ENNReal)
    (hμL : (μ : ENNReal) < L) (R : ℝ) (hR : 0 ≤ R)
    (H : Matrix (Fin N) (Fin N) ℝ) (b : Fin (N + 1) → ℝ)
    (C : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ) (hC : C.IsSymm)
    (d : ℕ) (hd : N + 2 ≤ d) :
    worstCase d μ L R H b C = sdpValue μ L R H b C := by sorry

end TaylorHGAudit.PEP
